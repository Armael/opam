open OpamCudfSolverSig

let log f = OpamConsole.log "open-wbo-inc (wrapper)" f
let logsolver f = OpamConsole.log "open-wbo-inc (solver)" f

let name = "open-wbo-inc"

let ext : string option ref = ref None

let command_name_s = "open-wbo-inc"
let command_name = Some command_name_s

let is_present =
  let present = lazy (
    OpamSystem.resolve_command command_name_s <> None
  ) in
  fun () -> Lazy.force present

let default_criteria = {
  crit_default = "-removed,\
                  -count[hidden-version,changed],\
                  -count[version-lag,request],\
                  -count[version-lag,changed],\
                  -count[missing-depexts,changed],\
                  -changed";
  crit_upgrade = "-removed,\
                  -count[hidden-version,changed],\
                  -count[version-lag,solution],\
                  -count[missing-depexts,changed],\
                  -new";
  crit_fixup = "-changed,\
                -count[hidden-version,changed],\
                -count[version-lag,solution],\
                -count[missing-depexts,changed]";
  crit_best_effort_prefix = Some "+count[opam-query,solution],";
}

(* Criteria *)

type filter = Installed | Changed | Removed | New | Upgraded | Downgraded | Requested
type property = string option
type sign = Plus | Minus

type criterion = sign * filter * property

(* Criteria parsing *)
(* Copy-paste from opamBuiltinZ3.ml.real *)
module Syntax = struct

  let criterion_of_string (s,params) =
    let sign = match s.[0] with
      | '+' -> Plus
      | '-' -> Minus
      | c -> failwith (Printf.sprintf "criteria_of_string sign=%c" c)
      | exception Invalid_argument _ ->
        failwith "criteria_of_string sign=EOF"
    in
    let s = String.sub s 1 (String.length s - 1) in
    let subset_of_string = function
      | "new" -> New
      | "removed" -> Removed
      | "changed" -> Changed
      | "up" -> Upgraded
      | "down" -> Downgraded
      | "installed" | "solution" -> Installed
      | "request" -> Requested
      | s -> failwith ("criteria_of_string subset="^s)
    in
    match s, params with
    | "count", [field; subset] ->
      sign, subset_of_string subset, Some field
    | s, [] -> sign, subset_of_string s, None
    | s, _ -> failwith ("criteria_of_string s="^s)
(*
  let string_of_criterion (sign, filter, property: criterion) =
    Printf.sprintf "%c%s%s"
      (match sign with Plus -> '+' | Minus -> '-')
      (match filter with
       | Installed -> "installed"
       | Changed -> "changed"
       | Removed -> "removed"
       | New -> "new"
       | Upgraded -> "up"
       | Downgraded -> "down"
       | Requested -> "request")
      (match property with None -> "" | Some p -> "["^p^"]")
*)
  let criteria_of_string s =
    let start = ref 0 in
    let crits = ref [] in
    let params = ref None in
    for i = 0 to String.length s - 1 do
      match s.[i] with
      | ',' ->
        let sub = String.sub s !start (i - !start) in
        start := i + 1;
        if sub <> "" then
          (match !params with
           | None -> crits := (sub, []) :: !crits
           | Some (name, ps) -> params := Some (name, sub :: ps))
      | '[' ->
        let sub = String.sub s !start (i - !start) in
        start := i + 1;
        if !params <> None then failwith "criteria_of_string";
        params := Some (sub, [])
      | ']' ->
        let sub = String.sub s !start (i - !start) in
        start := i + 1;
        (match !params with
         | None -> failwith "criteria_of_string"
         | Some (name, ps) ->
           params := None;
           crits := (name, List.rev (sub::ps)) :: !crits)
      | _ -> ()
    done;
    if !start < String.length s then
      crits := (String.sub s !start (String.length s - !start), []) :: !crits;
    if !params <> None then failwith "criteria_of_string";
    let r = List.rev_map criterion_of_string !crits in
    r

end

module Cnf : sig
  type lit = int
  type weight = Soft of int | Top

  type unweighted
  type weighted

  type ctx
  val mk_ctx : unit -> ctx
  val fresh_lit : ctx -> lit
  val max_lit : ctx -> lit

  module Clause : sig
    type _ t
    val singl : lit -> unweighted t
    val wsingl : lit:lit -> w:weight -> weighted t
    val disj : lit list -> unweighted t
    val wdisj : lits:lit list -> w:weight -> weighted t
    val lit_implies : lit -> 'a t -> 'a t
    val with_weight: _ t -> weight -> weighted t
    val weight: weighted t -> weight
    val fold: ('a -> lit -> 'a) -> 'a -> _ t -> 'a
  end

  type 'a t
  val empty : 'a t
  val and_clause : 'a t -> 'a Clause.t -> 'a t
  val neg_clause : unweighted Clause.t -> unweighted t
  val neg_wclause : ctx -> weighted Clause.t -> weighted t
  val and_ : 'a t -> 'a t -> 'a t
  val andl : 'a t list -> 'a t
  val clauses : 'a Clause.t list -> 'a t
  val fold : ('b -> 'a Clause.t -> 'b) -> 'b -> 'a t -> 'b
  val to_weighted : _ t -> weighted t
  val nclauses : 'a t -> int
end = struct
  type lit = int
  type weight = Soft of int | Top

  type unweighted = [`U]
  type weighted = [`W]

  type ctx = {
    mutable next_fresh_lit : int;
  }

  let mk_ctx () = { next_fresh_lit = 1 }

  let fresh_lit ctx =
    let lit = ctx.next_fresh_lit in
    ctx.next_fresh_lit <- lit + 1;
    lit

  let max_lit ctx =
    if ctx.next_fresh_lit = 1 then
      raise (Invalid_argument "Cnf.max_lit")
    else
      ctx.next_fresh_lit - 1

  module Clause = struct
    type _ t = int list (* disjunction *) * weight

    let singl x = ([x], Top)
    let wsingl ~lit ~w = ([lit], w)
    let disj l = (l, Top)
    let wdisj ~lits ~w = (lits, w)
    let lit_implies x (l, w) = (-x :: l, w) (* A => B  ==  ¬A \/ B *)
    let with_weight (l, _) w = (l, w)
    let weight (_, w) = w
    let fold f acc (l, _) = List.fold_left f acc l
  end

  type 'a t = 'a Clause.t list (* conjunction *)

  let empty = []
  let and_clause cnf cl = cl :: cnf
  let neg_clause (cl, _) =
    (* ¬ (A \/ B \/ ...)  == ¬A /\ ¬B /\ ... *)
    List.map (fun lit -> ([- lit], Top)) cl
  let neg_wclause ctx (cl, w) =
    (* ¬ (A \/ B \/ ...), w

       ==

       P <=> ¬ (A \/ B \/ ...) /\
       P, w

       ==

       (¬ P \/ ¬ (A \/ B \/ ...)) /\
       (A \/ B \/ ... \/ P) /\
       P, w

       ==

       (¬ P \/ ¬A) /\ (¬P \/ ¬B) /\ ... /\ (A \/ B \/ ... P) /\
       P, w


       where P is a fresh literal
    *)
    let p = fresh_lit ctx in
    ([p], w) ::
    (p :: cl, Top) ::
    List.map (fun lit -> [-p; -lit], Top) cl
  let and_ cnf1 cnf2 = List.rev_append cnf1 cnf2
  let andl l = List.fold_left (fun x y -> and_ y x) [] l
  let clauses l = l
  let fold f acc cnf = List.fold_left f acc cnf
  let to_weighted cnf = cnf
  let nclauses = List.length
end

let ( @^ ) opt l = match opt with
  | None -> l
  | Some x -> x :: l

let xrmap f l =
  match List.fold_left (fun acc x -> f x @^ acc) [] l with
  | [] -> None
  | l -> Some l

open OpamStd.Option.Op

type indexed_pkgs = {
  get_id : Cudf.package -> Cnf.lit option;
  get_id_exn : Cudf.package -> Cnf.lit;
  get_pkg : Cnf.lit -> Cudf.package;
}

let index_pkgs universe: Cnf.ctx * indexed_pkgs =
  let pkg_table : (Cudf.package, int) Hashtbl.t = Hashtbl.create 2731 in
  let pkg_rev_table : (int, Cudf.package) Hashtbl.t = Hashtbl.create 2731 in
  let pkg_id p = Hashtbl.find_opt pkg_table p in
  let pkg_of_id id = Hashtbl.find pkg_rev_table id in
  let pkg_id_exn p = match pkg_id p with Some x -> x | None -> raise Not_found in
  let ctx = Cnf.mk_ctx () in

  Cudf.iter_packages (fun pkg ->
      let id = Cnf.fresh_lit ctx in
      Hashtbl.add pkg_table pkg id;
      Hashtbl.add pkg_rev_table id pkg;
  ) universe;

  ctx,
  { get_id = pkg_id;
    get_id_exn = pkg_id_exn;
    get_pkg = pkg_of_id; }

let def_packages (_preamble, universe, _request) (pid: indexed_pkgs):
  Cnf.unweighted Cnf.t
  =
  let cnf = ref Cnf.empty in
  let push_clause c = cnf := Cnf.and_clause !cnf c in

  (* "keep" flags *)
  Cudf.iter_packages_by_name (fun _name pkgs ->
    let keep =
      match List.find (fun p -> p.Cudf.keep = `Keep_version) pkgs with
      | p -> pid.get_id p >>| fun x -> Cnf.Clause.singl x
      | exception Not_found ->
        if List.exists (fun p -> p.Cudf.keep = `Keep_package) pkgs then
          xrmap pid.get_id pkgs >>| Cnf.Clause.disj
        else None
    in
    OpamStd.Option.iter push_clause keep
  ) universe;

  let expand_constraint pkg (name, constr) =
    xrmap (fun p -> if Cudf.( =% ) pkg p then None else pid.get_id p)
      (Cudf.lookup_packages universe ~filter:constr name)
  in

  Cudf.iter_packages (fun pkg ->
      let pid = pid.get_id_exn pkg in
      (* depends *)
      List.iter (fun clause ->
          let expanded_clause =
            OpamStd.List.filter_map (expand_constraint pkg) clause
            |> List.flatten
            |> Cnf.Clause.disj
          in
          push_clause (Cnf.Clause.lit_implies pid expanded_clause)
        ) pkg.Cudf.depends (* is in cnf, cf Cudf_types *);

      (* conflicts *)
      List.iter (fun vpkg ->
          expand_constraint pkg vpkg |> OpamStd.Option.iter (fun l ->
              List.iter (fun conflicting ->
                  push_clause (Cnf.Clause.lit_implies pid
                                 (Cnf.Clause.singl (- conflicting)))
                ) l
            )
        ) pkg.Cudf.conflicts (* list of conflicts *);
    ) universe;

  !cnf

let def_request (_preamble, universe, request) (pid: indexed_pkgs):
  Cnf.unweighted Cnf.t
  =
  let expand_constraint (name, constr) =
    xrmap pid.get_id
      (Cudf.lookup_packages universe ~filter:constr name)
  in
  let inst =
    xrmap (fun vpkg -> expand_constraint vpkg >>| Cnf.Clause.disj)
      request.Cudf.install
    >>| Cnf.clauses
  in
  let rem =
    xrmap
      (fun vpkg -> expand_constraint vpkg
        >>| Cnf.Clause.disj
        >>| Cnf.neg_clause)
      request.Cudf.remove
    >>| Cnf.andl
  in
  let up =
    xrmap (fun (name, constr) ->
        match Cudf.get_installed universe name with
        | [] ->
          xrmap pid.get_id
            (Cudf.lookup_packages universe ~filter:constr name)
          >>| Cnf.Clause.disj
        | p::l ->
          let vmin =
            List.fold_left (fun vmin p -> max vmin p.Cudf.version) p.Cudf.version l
          in
          Cudf.lookup_packages universe ~filter:constr name |>
          List.filter (fun p -> p.Cudf.version > vmin) |>
          xrmap pid.get_id >>|
          (* fixme: the spec states that an 'upgrade' request should guarantee
             that only one version of the package will be installed. Since it's
             already a constraint in opam, and it's non trivial to encode, we
             ignore it here. *)
          Cnf.Clause.disj)
      request.Cudf.upgrade
    >>| Cnf.clauses
  in
  Cnf.andl @@ List.map (fun o -> o +! Cnf.empty) [inst; rem; up]

let read_pkg_property_value preamble property p =
  match property with
  | None -> 1
  | Some prop ->
    match Cudf.lookup_typed_package_property p prop with
    | `Int n | `Nat n -> n
    | `Bool true -> 1
    | `Bool false -> 0
    | _ -> 0
    | exception Not_found ->
      match List.assoc prop preamble.Cudf.property with
      | `Int (Some n) | `Nat (Some n) -> n
      | `Bool (Some true) -> 1
      | `Bool (Some false) -> 0
      | _ -> 0
      | exception Not_found ->
        failwith ("Undefined CUDF property: "^prop)

let def_criterion (ctx: Cnf.ctx)  (preamble, universe, request) (pid: indexed_pkgs)
    (sign, filter, property : criterion) :
  Cnf.weighted Cnf.t
  =
  let renormalize_property_value =
    (* Renormalize version-lag across packages *)
    (* XXX should this be done at a upper level? *)
    if property = Some "version-lag" then begin
      let pkg_max_version_lag : (Cudf_types.pkgname, int) Hashtbl.t =
        Hashtbl.create 1731 in
      Cudf.iter_packages_by_name (fun pkgname pkgvers ->
          let max_version_lag =
            List.fold_left (fun m pkgver ->
                max m (read_pkg_property_value preamble property pkgver))
              0 pkgvers
          in
          assert (not (Hashtbl.mem pkg_max_version_lag pkgname));
          Hashtbl.replace pkg_max_version_lag pkgname max_version_lag
        ) universe;
      let overall_max_version_lag =
        Hashtbl.fold (fun _ -> max) pkg_max_version_lag 0 in
      fun pkg v ->
        let pkg_max_ver_lag =
          Hashtbl.find pkg_max_version_lag pkg.Cudf.package in
        (* renormalize *)
        (v * overall_max_version_lag) / pkg_max_ver_lag
    end else (fun _pkg v -> v)
  in
  let prop_val pkg =
    read_pkg_property_value preamble property pkg
    |> renormalize_property_value pkg
  in

  (* /!\ make sure that weights are >= 1. A prop value of 0 means that we drop
     the clause. *)
  let cnf : Cnf.weighted Cnf.t =
    let add_clause cnf (cl: Cnf.unweighted Cnf.Clause.t) (pv: int) =
      if pv = 0 then
        cnf
      else if pv > 0 then
        Cnf.and_clause cnf (Cnf.Clause.with_weight cl (Cnf.Soft pv))
      else (* pv < 0 *)
        Cnf.and_ (Cnf.neg_wclause ctx
                    (Cnf.Clause.with_weight cl (Cnf.Soft (-pv))))
          cnf
    in
    let module Cl = Cnf.Clause in

    match filter with
    | Installed ->
      Cudf.fold_packages (fun cnf pkg ->
          add_clause cnf (Cl.singl @@ pid.get_id_exn pkg) (prop_val pkg)
        ) Cnf.empty universe

    | Changed ->
      Cudf.fold_packages (fun cnf pkg ->
          add_clause cnf
            (if pkg.Cudf.installed then
               Cl.singl @@ - pid.get_id_exn pkg
             else
               Cl.singl @@ pid.get_id_exn pkg)
            (prop_val pkg)
        ) Cnf.empty universe

    | Removed ->
      Cudf.fold_packages (fun cnf pkg ->
          if pkg.Cudf.installed then
            let pkg_any_version =
              Cudf.lookup_packages universe pkg.Cudf.package
              |> List.map pid.get_id_exn
              |> Cl.disj in
            (* add the negated(!) clause *)
            add_clause cnf pkg_any_version (- (prop_val pkg))
          else cnf
        ) Cnf.empty universe

    | New ->
      Cudf.fold_packages (fun cnf pkg ->
          if pkg.Cudf.installed then cnf else
            add_clause cnf (Cl.singl @@ pid.get_id_exn pkg) (prop_val pkg)
        ) Cnf.empty universe

    | Upgraded ->
      Cudf.fold_packages (fun cnf pkg ->
          if pkg.Cudf.installed then cnf
          else match Cudf.get_installed universe pkg.Cudf.package with
            | [] -> cnf
            | l when List.for_all (fun p -> p.Cudf.version < pkg.Cudf.version) l ->
              add_clause cnf (Cl.singl @@ pid.get_id_exn pkg) (prop_val pkg)
            | _ -> cnf
        ) Cnf.empty universe

    | Downgraded ->
      Cudf.fold_packages (fun cnf pkg ->
          if pkg.Cudf.installed then cnf
          else match Cudf.get_installed universe pkg.Cudf.package with
            | [] -> cnf
            | l when List.for_all (fun p -> p.Cudf.version > pkg.Cudf.version) l ->
              add_clause cnf (Cl.singl @@ pid.get_id_exn pkg) (prop_val pkg)
            | _ -> cnf
        ) Cnf.empty universe

    | Requested ->
      Cudf.fold_packages (fun cnf pkg ->
          if
            List.exists (fun (name, cstr) ->
                pkg.Cudf.package = name &&
                Cudf.version_matches pkg.Cudf.version cstr
              ) request.Cudf.install ||
            List.exists (fun (name, cstr) ->
                pkg.Cudf.package = name &&
                Cudf.version_matches pkg.Cudf.version cstr
              ) request.Cudf.upgrade
          then
            add_clause cnf (Cl.singl @@ pid.get_id_exn pkg) (prop_val pkg)
          else
            cnf
        ) Cnf.empty universe
  in

  match sign with
  | Plus ->
    cnf
  | Minus ->
    (* Negate the clauses *)
    Cnf.fold (fun acc clause -> Cnf.and_ (Cnf.neg_wclause ctx clause) acc)
      Cnf.empty cnf


let def_criteria ctx cudf pid (criteria: criterion list): Cnf.weighted Cnf.t =
  (* Criteria are hierarchical, with the more important one coming first, etc. *)
  let criteria_cnf = List.map (def_criterion ctx cudf pid) criteria in

  (* rescale weights to encode the hierarchy: the base weight of a level is the
     sum of the weights of the level below, plus one. *)
  List.fold_right (fun level_cnf (cnf, level_base_weight) ->
      let cnf, level_weights_sum =
        Cnf.fold (fun (cnf, level_weights_sum) cl ->
            match Cnf.Clause.weight cl with
            | Cnf.Top ->
              (Cnf.and_clause cnf cl, level_weights_sum)
            | Cnf.Soft w ->
              let w' = level_base_weight + w in
              (Cnf.and_clause cnf (Cnf.Clause.with_weight cl (Cnf.Soft w')),
               level_weights_sum + w')
          ) (cnf, 0) level_cnf
      in
      (cnf, level_weights_sum + 1)
    ) criteria_cnf (Cnf.empty, 0)
  |> fst

let output_wcnf (cout: out_channel) (ctx: Cnf.ctx) (cnf: Cnf.weighted Cnf.t) =
  let weights_sum = Cnf.fold (fun s clause ->
      match Cnf.Clause.weight clause with
      | Top -> s
      | Soft w -> s + w
    ) 0 cnf
  in
  let top = weights_sum + 1 in
  let max_lit = Cnf.max_lit ctx in

  let output_clause cl =
    let w =
      match Cnf.Clause.weight cl with
      | Top -> top
      | Soft w -> w
    in
    Printf.fprintf cout "%d " w;
    Cnf.Clause.fold (fun () lit -> Printf.fprintf cout "%d " lit) () cl;
    Printf.fprintf cout "0\n"
  in

  Printf.fprintf cout "p wcnf %d %d %d\n" max_lit (Cnf.nclauses cnf) top;
  (* Not required by the format, but output hard clauses first *)
  Cnf.fold (fun () cl -> if Cnf.Clause.weight cl = Top then output_clause cl) () cnf;
  Cnf.fold (fun () cl -> if Cnf.Clause.weight cl <> Top then output_clause cl) () cnf

type solver_result =
  | Optimum_found of Cudf.package list
  | Sat of Cudf.package list
  | Unsat
  | Unknown

let parse_solver_output (pid: indexed_pkgs) (output: string list): solver_result =
  let s_line =
    try
      List.find (OpamStd.String.starts_with ~prefix:"s ") output
      |> OpamStd.String.remove_prefix ~prefix:"s "
      |> OpamStd.String.strip
    with Not_found ->
      raise (Common.CudfSolver.Error "Ill-formed output: no solution status")
  in
  let get_solution () =
    let values =
      try
        List.find (OpamStd.String.starts_with ~prefix:"v ") output
        |> OpamStd.String.remove_prefix ~prefix:"v "
        |> OpamStd.String.strip
        |> (fun s -> OpamStd.String.split s ' ')
      with Not_found ->
        raise (Common.CudfSolver.Error "Ill-formed output: no solution values")
    in
    OpamStd.List.filter_map (fun s ->
        try
          let x = int_of_string s in
          if x > 0 then (
            let pkg = pid.get_pkg x in
            Some { pkg with Cudf.was_installed = pkg.Cudf.installed;
                            Cudf.installed = true }
          ) else None
        with Not_found | Invalid_argument _ ->
          raise (Common.CudfSolver.Error
                   ("Ill-formed output: invalid solution literal " ^ s))
      ) values
  in
  match s_line with
  | "OPTIMUM FOUND" -> Optimum_found (get_solution ())
  | "SATISFIABLE" -> Sat (get_solution ())
  | "UNSATISFIABLE" -> Unsat
  | "UNKNOWN" -> Unknown
  | _ ->
    raise (Common.CudfSolver.Error
             ("Ill-formed output: unknown solution status " ^ s_line))

let call ~criteria ?(timeout = 60.) (preamble, universe, _ as cudf) =
  log "Generating package definitions";
  let ctx, pid = index_pkgs universe in
  let pkgs_cnf = def_packages cudf pid in
  log "Generating request";
  let req_cnf = def_request cudf pid in
  log "Generating optimization criteria";
  let criteria = Syntax.criteria_of_string criteria in
  let criteria_cnf =def_criteria ctx cudf pid criteria in
  let cnf =
    Cnf.andl [
      Cnf.to_weighted pkgs_cnf;
      Cnf.to_weighted req_cnf;
      criteria_cnf
    ]
  in
  log "Resolving...";
  let solver_in =
    OpamFilename.of_string (OpamSystem.temp_file "solver-open-wbo-inc-in") in
  try
    let () =
      let oc = OpamFilename.open_out solver_in in
      output_wcnf oc ctx cnf;
      close_out oc
    in
    let cmd =
      OpamProcess.command
        ~name:"open-wbo-inc"
        ~allow_stdin:false
        ~verbose:(OpamCoreConfig.(abs !r.debug_level >= 2))
        "timeout"
        ["-s"; "15"; (* SIGTERM *)
         string_of_int (int_of_float timeout);
         command_name_s;
         "-ca=1";
         (* number of clusters; not sure whether the +1 is necessary *)
         "-c=" ^ string_of_int (List.length criteria + 1);
         "-algorithm=6";
         OpamFilename.to_string solver_in]
    in
    let cmd_res = OpamProcess.run cmd in
    OpamFilename.remove solver_in;
    OpamProcess.cleanup cmd_res;
    let solver_res = parse_solver_output pid cmd_res.r_stdout in
    begin match solver_res with
      | Optimum_found pkgs ->
        logsolver "Optimum found";
        pkgs
      | Sat pkgs ->
        logsolver "Solution found (possibly non optimal)";
        pkgs
      | Unsat ->
        raise Common.CudfSolver.Unsat
      | Unknown ->
        raise (Common.CudfSolver.Error "unknown error")
    end |>
    Cudf.load_universe |>
    fun u -> Some preamble, u
  with e ->
    OpamStd.Exn.finalise e @@ fun () ->
    OpamFilename.remove solver_in
