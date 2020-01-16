(**************************************************************************)
(*                                                                        *)
(*    Copyright 2012-2015 OCamlPro                                        *)
(*    Copyright 2012 INRIA                                                *)
(*                                                                        *)
(*  All rights reserved. This file is distributed under the terms of the  *)
(*  GNU Lesser General Public License version 2.1, with the special       *)
(*  exception on linking described in the file LICENSE.                   *)
(*                                                                        *)
(**************************************************************************)

open OpamStd.Op
open OpamProcess.Job.Op

let log fmt = OpamConsole.log "PARALLEL" fmt
let slog = OpamConsole.slog

exception Aborted

module type VERTEX = sig
  include OpamStd.OrderedType
  include Graph.Sig.COMPARABLE with type t := t
end

type dependency_label = unit

module type G = sig
  include Graph.Sig.I with type E.label = dependency_label
  module Vertex: VERTEX with type t = V.t
  module Topological: sig
    val fold: (V.t -> 'a -> 'a) -> t -> 'a -> 'a
  end
  val iter: ?pre:(V.t -> unit) -> ?post:(V.t -> unit) -> t -> unit
  val has_cycle: t -> bool
  val scc_list: t -> V.t list list
end

module type SIG = sig

  module G : G

  val iter:
    jobs:int ->
    command:(pred:(G.V.t * 'a) list -> G.V.t -> 'a OpamProcess.job) ->
    ?dry_run:bool ->
    ?pools:((G.V.t list * int) list) ->
    G.t ->
    unit

  val map:
    jobs:int ->
    command:(pred:(G.V.t * 'a) list -> G.V.t -> 'a OpamProcess.job) ->
    ?dry_run:bool ->
    ?pools:((G.V.t list * int) list) ->
    G.t ->
    (G.V.t * 'a) list

  exception Errors of G.V.t list * (G.V.t * exn) list * G.V.t list
  exception Cyclic of G.V.t list list
end

module Make (G : G) = struct

  module G = G

  module V = G.Vertex
  module M = OpamStd.Map.Make (V)
  module S = OpamStd.Set.Make (V)

  (* naive implementation of priority queues as sets *)
  module PQueue : sig
    type t

    val empty : t
    val add : V.t -> priority:int -> t -> t
    val is_empty : t -> bool
    val take_opt : t -> (t * V.t) option
    val take : t -> t * V.t
  end = struct
    module S = Set.Make (struct
        type t = V.t * int
        let compare (u, p) (v, q) =
          match - (compare p q) with
          | 0 -> V.compare u v
          | z -> z
      end)

    type t = S.t
    let empty = S.empty
    let add v ~priority s = S.add (v, priority) s
    let is_empty = S.is_empty
    let take_opt s =
      match S.min_elt_opt s with
      | Some ((v, _) as elt) ->
        let s' = S.remove elt s in
        Some (s', v)
      | None -> None
    let take s =
      match take_opt s with
      | Some x -> x
      | None -> failwith "PQueue.take"
  end

  exception Errors of G.V.t list * (G.V.t * exn) list * G.V.t list
  exception Cyclic of V.t list list

  open S.Op

  (* Returns a map (node -> return value) *)
  let aux_map ~jobs ~command ?(dry_run=false) ?(pools=[]) g =
    log "Iterate over %a task(s) with %d process(es)"
      (slog @@ G.nb_vertex @> string_of_int) g jobs;

    let njobs = G.nb_vertex g in

    let all_jobs = G.fold_vertex S.add g S.empty in

    let pools =
      let defined =
        List.map (fun (elts, jobs) -> S.of_list elts, jobs)
          pools
      in
      let default =
        List.fold_left (fun acc (pool, _) -> acc -- pool)
          all_jobs defined, jobs
      in
      default :: defined
    in

    (* mapping task -> pool ids *)
    let _, pools_of_task = List.fold_left (fun (i, pools_of_task) (pool, _) ->
        i + 1,
        S.fold (fun task pools_of_task ->
            M.add task (i :: try M.find task pools_of_task with Not_found -> [])
              pools_of_task
          ) pool pools_of_task
      ) (0, M.empty) pools
    in

    if G.has_cycle g then (
      let sccs = G.scc_list g in
      let sccs = List.filter (function _::_::_ -> true | _ -> false) sccs in
      raise (Cyclic sccs)
    );

    let nb_revdeps_of_vertex =
      let r = ref M.empty in
      let nb v = try M.find v !r with Not_found -> 0 in
      let upd v n = r := M.add v n !r in
      G.iter
        ~post:(fun v ->
            let transitive_revdeps =
              List.fold_left (fun sum w -> sum + nb w) 0 (G.succ g v) in
            upd v (transitive_revdeps + G.out_degree g v))
        g;
      !r
    in

    let print_status
        (finished: int)
        (running: (int * OpamProcess.t * _ * string option) M.t) =
      let texts =
        OpamStd.List.filter_map (fun (_,_,_,t) -> t) (M.values running) in
      let rec limit_width acc rem_cols = function
        | [] -> List.rev acc
        | t::ts ->
          let len = OpamStd.Format.visual_length t in
          if ts = [] && len < rem_cols then List.rev (t::acc)
          else if len > rem_cols - 5 then
            List.rev
              (Printf.sprintf "%s+%2d"
                 (String.make (rem_cols - 4) ' ') (List.length ts + 1)
               :: acc)
          else
            limit_width (t::acc) (rem_cols - len - 1) ts
      in
      let title =
        Printf.sprintf "Processing %2d/%d:"
          (finished + M.cardinal running) njobs
      in
      let texts =
        if OpamConsole.disp_status_line () then
          limit_width [] (OpamStd.Sys.terminal_columns ()) (title::texts)
        else if OpamConsole.verbose () then title::texts
        else []
      in
      if texts <> [] then OpamConsole.status_line "%s" (String.concat " " texts)
    in

    let rec loop
        (results: 'b M.t)
        (running: (int *
                   OpamProcess.t *
                   (OpamProcess.result -> 'b OpamProcess.job) *
                   string option
                  ) M.t)
        (ready: PQueue.t array)
        (free_slots: int array)
      =
      let run_seq_command n pool_id (job: 'b OpamProcess.job): 'b M.t =
        match job with
        | Done r ->
          log "Job %a finished" (slog (string_of_int @* V.hash)) n;
          let results = M.add n r results in
          let running =
            if M.mem n running then M.remove n running else running in
          if not (M.is_empty running) then
            print_status (M.cardinal results) running;
          free_slots.(pool_id) <- free_slots.(pool_id) + 1;
          List.iter (fun m ->
              if not (M.mem m running) &&
                 not (M.mem m results) &&
                 List.for_all (fun n -> M.mem n results) (G.pred g m)
              then begin
                let m_pools = try M.find m pools_of_task with Not_found -> failwith "b" in
                List.iter (fun pool ->
                    let priority = try M.find m nb_revdeps_of_vertex with Not_found -> failwith "c" in
                    ready.(pool) <- PQueue.add m ~priority ready.(pool)
                  ) m_pools
              end
            ) (G.succ g n);
          loop results running ready free_slots
        | Run (cmd, cont) ->
          log "Next task in job %a: %a" (slog (string_of_int @* V.hash)) n
            (slog OpamProcess.string_of_command) cmd;
          let p =
            if dry_run then OpamProcess.dry_run_background cmd
            else OpamProcess.run_background cmd
          in
          let running =
            M.add n (pool_id, p, cont, OpamProcess.text_of_command cmd) running
          in
          print_status (M.cardinal results) running;
          loop results running ready free_slots
      in

      let fail node error =
        log "Exception while computing job %a: %a"
          (slog (string_of_int @* V.hash)) node
          (slog V.to_string) node;
        if error = Sys.Break then OpamConsole.error "User interruption";
        let running = M.remove node running in
        (* Cleanup *)
        let errors,pend =
          if dry_run then [node,error],[] else
            M.fold (fun n (_,p,cont,_text) (errors,pend) ->
              try
                match OpamProcess.dontwait p with
                | None -> (* process still running *)
                  OpamProcess.interrupt p;
                  (n,Aborted) :: errors,
                  p::pend
                | Some result ->
                  match cont result with
                  | Done _ -> errors, pend
                  | Run _ ->
                    (n,Aborted) :: errors,
                    pend
              with
              | Unix.Unix_error _ -> errors, pend
              | e -> (n,e)::errors, pend)
            running ([node,error],[])
        in
        (try List.iter (fun _ -> ignore (OpamProcess.wait_one pend)) pend
         with e -> log "%a in sub-process cleanup" (slog Printexc.to_string) e);
        (* Generate the remaining nodes in topological order *)
        let remaining =
          G.Topological.fold (fun n remaining ->
              if M.mem n results || List.mem_assoc n errors then remaining
              else n::remaining)
            g [] in
        raise (Errors (M.keys results, List.rev errors, List.rev remaining))
      in

      if M.is_empty running && Array.for_all PQueue.is_empty ready then
        results
      else
      let rec find_ready_pool i =
        if i >= Array.length ready then None
        else if free_slots.(i) > 0 &&
                not (PQueue.is_empty ready.(i))
        then Some i
        else find_ready_pool (i+1)
      in
      match find_ready_pool 0 with
      | Some pool ->
        (* Start a new process *)
        let pq, n = PQueue.take ready.(pool) in
        ready.(pool) <- pq;
        if not (M.mem n running) && not (M.mem n results) then begin
          log "Starting job %a (worker %a): %a"
            (slog (string_of_int @* V.hash)) n
            (* (slog
             *    (fun pools ->
             *       let slots = get_slots nslots n in
             *       OpamStd.List.concat_map " " (fun (pool, jobs) ->
             *           let nslots =
             *             OpamStd.Option.of_Not_found (List.assoc pool) slots
             *           in
             *           Printf.sprintf "%s/%d"
             *             (match nslots with
             *              | None -> "-"
             *              | Some n -> string_of_int (jobs - n + 1))
             *             jobs)
             *         pools))
             * pools *)
            (slog (fun x -> x)) "??"
            (slog V.to_string) n;
          let pred = G.pred g n in
          let pred = List.map (fun n -> n, try M.find n results with Not_found -> failwith "d") pred in
          let cmd = try command ~pred n with e -> fail n e in
          free_slots.(pool) <- free_slots.(pool) - 1;
          run_seq_command n pool cmd
        end else
          loop results running ready free_slots
      | None ->
        (* Wait for a process to end *)
        let processes =
          M.fold (fun n (id,p,x,_) acc -> (p,(n,(x,id))) :: acc) running []
        in
        let process, result =
          if dry_run then
            OpamProcess.dry_wait_one (List.map fst processes)
          else try match processes with
            | [p,_] -> p, OpamProcess.wait p
            | _ -> OpamProcess.wait_one (List.map fst processes)
            with e -> fail (fst (snd (List.hd processes))) e
        in
        let n, (cont, pool_id) = List.assoc process processes in
        log "Collected task for job %a (ret:%d)"
          (slog (string_of_int @* V.hash)) n result.OpamProcess.r_code;
        let next : 'b OpamProcess.job =
          try cont result with e ->
            OpamProcess.cleanup result;
            fail n e in
        OpamProcess.cleanup result;
        run_seq_command n pool_id next
    in

    let roots =
      G.fold_vertex
        (fun n roots -> if G.in_degree g n = 0 then S.add n roots else roots)
        g S.empty
    in

    let npools = List.length pools in
    let ready = Array.make npools PQueue.empty in
    let free_slots = Array.of_list (List.map snd pools) in

    S.iter (fun m ->
        let m_pools = M.find m pools_of_task in
        List.iter (fun pool ->
            let priority = M.find m nb_revdeps_of_vertex in
            ready.(pool) <- PQueue.add m ~priority ready.(pool)
          ) m_pools
      ) roots;

    let r = loop M.empty M.empty ready free_slots in
    OpamConsole.clear_status ();
    r

  let iter ~jobs ~command ?dry_run ?pools g =
    ignore (aux_map ~jobs ~command ?dry_run ?pools g)

  let map ~jobs ~command ?dry_run ?pools g =
    M.bindings (aux_map ~jobs ~command ?dry_run ?pools g)

  (* Only print the originally raised exception, which should come first. Ignore
     Aborted exceptions due to other commands termination, and simultaneous
     exceptions in other command's continuations (unlikely as that would require
     both commands to have terminated simultaneously) *)
  let error_printer = function
    | Errors (_, (_,exc)::_, _) -> Some (Printexc.to_string exc)
    | _ -> None

  let () = Printexc.register_printer error_printer
end

module type GRAPH = sig
  include Graph.Sig.I with type E.label = dependency_label
  include Graph.Oper.S with type g = t
  module Topological : sig
    val fold : (V.t -> 'a -> 'a) -> t -> 'a -> 'a
    val iter : (V.t -> unit) -> t -> unit
  end
  module Parallel : SIG with type G.t = t
                         and type G.V.t = vertex
  module Dot : sig val output_graph : out_channel -> t -> unit end
  val transitive_closure:  ?reflexive:bool -> t -> unit
  val build: V.t list -> E.t list -> t
  val compare : t -> t -> int
  val to_json : t OpamJson.encoder
  val of_json : t OpamJson.decoder
end

module MakeGraph (X: VERTEX) = struct
  module Vertex = X
  module PG = Graph.Imperative.Digraph.ConcreteBidirectional (Vertex)
  module Topological = Graph.Topological.Make (PG)
  module Traverse = Graph.Traverse.Dfs(PG)
  module Components = Graph.Components.Make(PG)
  module Parallel = Make (struct
      include PG
      module Vertex = Vertex
      module Topological = Topological
      include Traverse
      include Components
    end)
  module Dot = Graph.Graphviz.Dot (struct
      let edge_attributes _ = []
      let default_edge_attributes _ = []
      let get_subgraph _ = None
      let vertex_attributes _ = []
      let vertex_name v = Printf.sprintf "\"%s\"" (Vertex.to_string v)
      let default_vertex_attributes _ = []
      let graph_attributes _ = []
      include PG
    end)
  include PG
  include Graph.Oper.I (PG)

  let transitive_closure ?reflexive g =
    ignore (add_transitive_closure ?reflexive g)

  let build vertices edges =
    let graph = create ~size:(List.length vertices) () in
    List.iter (add_vertex graph) vertices;
    List.iter (add_edge_e graph) edges;
    graph

  let compare g1 g2 =
    let module Vertices = Set.Make(Vertex) in
    let module Edges = Set.Make(E) in
    let vertices g = fold_vertex Vertices.add g Vertices.empty in
    let edges g = fold_edges_e Edges.add g Edges.empty in
    match Vertices.compare (vertices g1) (vertices g2) with
    | 0 -> Edges.compare (edges g1) (edges g2)
    | n -> n

  let to_json (graph : t) : OpamJson.t =
    let vertex_map =
      (* we ensure that the map indexing respects the vertex ordering *)
       let module Vertices = Set.Make(Vertex) in
       let vertices = fold_vertex Vertices.add graph Vertices.empty in
       List.mapi (fun i v -> (i, v)) (Vertices.elements vertices)
    in
    let vertices =
      let vertex_to_json (i, v) = (string_of_int i, X.to_json v) in
      `O (List.map vertex_to_json vertex_map) in
    let edges =
      let vertex_inv_map = List.map (fun (i, v) -> (v, i)) vertex_map in
      let index v = List.assoc v vertex_inv_map in
      let index_to_json v = `String (string_of_int (index v)) in
      let edge_to_json edge =
        let () = E.label edge in
        (* labels carry no information; if this changes,
           we should add a "label" field in the JSON output *)
        `O [
          ("src", index_to_json (E.src edge));
          ("dst", index_to_json (E.dst edge));
        ] in
      `A (fold_edges_e (fun edge li -> edge_to_json edge :: li) graph [])
    in
    `O [
      ("vertices", vertices);
      ("edges", edges);
    ]

  let of_json : t OpamJson.decoder = function
    | `O dict ->
      begin try
          let vertices_json = match List.assoc "vertices" dict with
            | `O vertices -> vertices
            | _ -> raise Not_found in
          let edges_json = match List.assoc "edges" dict with
            | `A edges -> edges
            | _ -> raise Not_found in
          let vertex_map =
            let vertex_of_json (ij, vj) =
              let i = try int_of_string ij with _ -> raise Not_found in
              let v = match X.of_json vj with
                  | None -> raise Not_found
                  | Some v -> v in
              (i, v) in
            List.map vertex_of_json vertices_json
          in
          let edges =
            let int_of_jsonstring = function
              | `String s -> (try int_of_string s with _ -> raise Not_found)
              | _ -> raise Not_found in
            let find kj = List.assoc (int_of_jsonstring kj) vertex_map in
            let edge_of_json = function
              | `O dict ->
                let src = find (List.assoc "src" dict) in
                let label = () in
                let dst = find (List.assoc "dst" dict) in
                E.create src label dst
              | _ -> raise Not_found
            in List.map edge_of_json edges_json
          in
          Some (build (List.map snd vertex_map) edges)
        with Not_found -> None
      end
    | _ -> None
end

(* Simple polymorphic implem on lists when we don't need full graphs.
   We piggy-back on the advanced implem using an array and an int-graph *)
module IntGraph = MakeGraph(struct
    type t = int
    let compare x y = x - y
    let hash x = x
    let equal x y = x = y
    let to_string = string_of_int
    let to_json x = `Float (float_of_int x)
    let of_json = function
      | `Float x -> (try Some (int_of_float x) with _ -> None)
      | _ -> None
  end)

let flat_graph_of_array a =
  let g = IntGraph.create () in
  Array.iteri (fun i _ -> IntGraph.add_vertex g i) a;
  g

exception Errors = IntGraph.Parallel.Errors

let iter ~jobs ~command ?dry_run l =
  let a = Array.of_list l in
  let g = flat_graph_of_array a in
  let command ~pred:_ i = command a.(i) in
  ignore (IntGraph.Parallel.iter ~jobs ~command ?dry_run g)

let map ~jobs ~command ?dry_run l =
  let a = Array.of_list l in
  let g = flat_graph_of_array a in
  let command ~pred:_ i = command a.(i) in
  let r = IntGraph.Parallel.aux_map ~jobs ~command ?dry_run g in
  let rec mklist acc n =
    if n < 0 then acc
    else mklist (IntGraph.Parallel.M.find n r :: acc) (n-1)
  in
  mklist [] (Array.length a - 1)

let reduce ~jobs ~command ~merge ~nil ?dry_run l =
  let a = Array.of_list l in
  let g = flat_graph_of_array a in
  let command ~pred:_ i = command a.(i) in
  let r = IntGraph.Parallel.aux_map ~jobs ~command ?dry_run g in
  IntGraph.Parallel.M.fold (fun _ -> merge) r nil
