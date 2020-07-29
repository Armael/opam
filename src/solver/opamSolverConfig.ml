(**************************************************************************)
(*                                                                        *)
(*    Copyright 2015-2018 OCamlPro                                        *)
(*                                                                        *)
(*  All rights reserved. This file is distributed under the terms of the  *)
(*  GNU Lesser General Public License version 2.1, with the special       *)
(*  exception on linking described in the file LICENSE.                   *)
(*                                                                        *)
(**************************************************************************)

type t = {
  cudf_file: string option;
  solver: (module OpamCudfSolver.S) Lazy.t;
  best_effort: bool;
  (* The following are options because the default can only be known once the
     solver is known, so we set it only if no customisation was made *)
  solver_preferences_default: string option Lazy.t;
  solver_preferences_upgrade: string option Lazy.t;
  solver_preferences_fixup: string option Lazy.t;
  solver_preferences_best_effort_prefix: string option Lazy.t;
  solver_timeout: float option;
}

type 'a options_fun =
  ?cudf_file:string option ->
  ?solver:((module OpamCudfSolver.S) Lazy.t) ->
  ?best_effort:bool ->
  ?solver_preferences_default:string option Lazy.t ->
  ?solver_preferences_upgrade:string option Lazy.t ->
  ?solver_preferences_fixup:string option Lazy.t ->
  ?solver_preferences_best_effort_prefix:string option Lazy.t ->
  ?solver_timeout:float option ->
  'a

let default =
  let solver = lazy (
    OpamCudfSolver.get_solver OpamCudfSolver.default_solver_selection
  ) in
  {
    cudf_file = None;
    solver;
    best_effort = false;
    solver_preferences_default = lazy None;
    solver_preferences_upgrade = lazy None;
    solver_preferences_fixup = lazy None;
    solver_preferences_best_effort_prefix = lazy None;
    solver_timeout = Some 60.;
  }

let setk k t
    ?cudf_file
    ?solver
    ?best_effort
    ?solver_preferences_default
    ?solver_preferences_upgrade
    ?solver_preferences_fixup
    ?solver_preferences_best_effort_prefix
    ?solver_timeout
  =
  let (+) x opt = match opt with Some x -> x | None -> x in
  k {
    cudf_file = t.cudf_file + cudf_file;
    solver = t.solver + solver;
    best_effort = t.best_effort + best_effort;
    solver_preferences_default =
      t.solver_preferences_default + solver_preferences_default;
    solver_preferences_upgrade =
      t.solver_preferences_upgrade + solver_preferences_upgrade;
    solver_preferences_fixup =
      t.solver_preferences_fixup + solver_preferences_fixup;
    solver_preferences_best_effort_prefix =
      t.solver_preferences_best_effort_prefix +
      solver_preferences_best_effort_prefix;
    solver_timeout =
      t.solver_timeout + solver_timeout;
  }

let set t = setk (fun x () -> x) t

let r = ref default

let update ?noop:_ = setk (fun cfg () -> r := cfg) !r

let with_auto_criteria config =
  let criteria = lazy (
    let module S = (val Lazy.force config.solver) in
    S.default_criteria
  ) in
  set config
    ~solver_preferences_default:
      (lazy (match config.solver_preferences_default with
           | lazy None -> Some (Lazy.force criteria).OpamCudfSolver.crit_default
           | lazy some -> some))
    ~solver_preferences_upgrade:
      (lazy (match config.solver_preferences_upgrade with
           | lazy None -> Some (Lazy.force criteria).OpamCudfSolver.crit_upgrade
           | lazy some -> some))
    ~solver_preferences_fixup:
      (lazy (match config.solver_preferences_fixup with
           | lazy None -> Some (Lazy.force criteria).OpamCudfSolver.crit_fixup
           | lazy some -> some))
    ~solver_preferences_best_effort_prefix:
      (lazy (match config.solver_preferences_best_effort_prefix with
           | lazy None ->
             (Lazy.force criteria).OpamCudfSolver.crit_best_effort_prefix
           | lazy some -> some))
    ()

let initk k =
  let open OpamStd.Config in
  let open OpamStd.Option.Op in
  let solver =
    let open OpamCudfSolver in
    match env_string "EXTERNALSOLVER" with
    | Some "" -> lazy (get_solver ~internal:true default_solver_selection)
    | Some s -> lazy (solver_of_string s)
    | None ->
      let internal = env_bool "USEINTERNALSOLVER" ++ env_bool "NOASPCUD" in
      lazy (get_solver ?internal default_solver_selection)
  in
  let best_effort =
    env_bool "BESTEFFORT" in
  let criteria =
    env_string "CRITERIA" >>| fun c -> lazy (Some c) in
  let upgrade_criteria =
    (env_string "UPGRADECRITERIA" >>| fun c -> lazy (Some c)) ++ criteria in
  let fixup_criteria =
    env_string "FIXUPCRITERIA" >>| fun c -> (lazy (Some c)) in
  let best_effort_prefix_criteria =
    env_string "BESTEFFORTPREFIXCRITERIA" >>| fun c -> (lazy (Some c)) in
  let solver_timeout =
    env_float "SOLVERTIMEOUT" >>| fun f -> if f <= 0. then None else Some f in
  setk (setk (fun c -> r := with_auto_criteria c; k)) !r
    ~cudf_file:(env_string "CUDFFILE")
    ~solver
    ?best_effort
    ?solver_preferences_default:criteria
    ?solver_preferences_upgrade:upgrade_criteria
    ?solver_preferences_fixup:fixup_criteria
    ?solver_preferences_best_effort_prefix:best_effort_prefix_criteria
    ?solver_timeout

let init ?noop:_ = initk (fun () -> ())

let best_effort =
  let r = lazy (
    !r.best_effort &&
    let crit = match Lazy.force !r.solver_preferences_default with
      | Some c -> c
      | None -> failwith "Solver criteria uninitialised"
    in
    let pfx = Lazy.force !r.solver_preferences_best_effort_prefix in
    pfx <> None ||
    OpamStd.String.contains ~sub:"opam-query" crit ||
    (OpamConsole.warning
       "Your solver configuration does not support --best-effort, the option \
        was ignored (you need to specify variable OPAMBESTEFFORTCRITERIA, or \
        set your criteria to maximise the count for cudf attribute \
        'opam-query')";
     false)
  ) in
  fun () -> Lazy.force r

let criteria kind =
  let crit = match kind with
    | `Default -> !r.solver_preferences_default
    | `Upgrade -> !r.solver_preferences_upgrade
    | `Fixup -> !r.solver_preferences_fixup
  in
  let str =
    match Lazy.force crit with
    | Some c -> c
    | None -> failwith "Solver criteria uninitialised"
  in
  if !r.best_effort then
    match !r.solver_preferences_best_effort_prefix with
    | lazy (Some pfx) -> pfx ^ str
    | lazy None -> str
  else str

let solution_score criteria preamble request universe_before universe =
  let criteria = OpamSolverCriteria.of_string criteria in
  let was_installed p =
    (Cudf.lookup_package universe_before (p.Cudf.package, p.Cudf.version)).
      Cudf.installed
  in
  let filtered_pkgs f =
    let filter =
      match f with
      | OpamSolverCriteria.Installed -> fun p -> p.Cudf.installed
      | Changed -> fun p -> p.Cudf.installed <> was_installed p
      | Removed -> fun p -> was_installed p && not p.Cudf.installed
      | New -> fun p -> not (was_installed p) && p.Cudf.installed
      | Upgraded -> fun p ->
        p.Cudf.installed &&
        List.exists was_installed @@
        Cudf.lookup_packages ~filter:(Some (`Lt, p.Cudf.version)) universe
          p.Cudf.package
      | Downgraded -> fun p ->
        p.Cudf.installed &&
        List.exists was_installed @@
        Cudf.lookup_packages ~filter:(Some (`Gt, p.Cudf.version)) universe
          p.Cudf.package
      | Requested -> fun p ->
        List.exists (fun (name, cstr) ->
            p.Cudf.package = name && Cudf.version_matches p.Cudf.version cstr)
          request.Cudf.install ||
        List.exists (fun (name, cstr) ->
            p.Cudf.package = name && Cudf.version_matches p.Cudf.version cstr)
          request.Cudf.upgrade
    in
    Cudf.get_packages ~filter universe
  in
  List.map (fun (sign, filter, property) ->
      let pkgs = filtered_pkgs filter in
      let score =
        List.fold_left (fun score pkg ->
            score +
            OpamSolverCriteria.read_pkg_property_value preamble property pkg
          ) 0 pkgs
      in
      match sign with
      | OpamSolverCriteria.Plus ->
        score
      | Minus ->
        - score
    ) criteria

let call_solver ~criteria (preamble, universe_before, request as cudf) =
  let module S = (val Lazy.force (!r.solver)) in
  OpamConsole.log "SOLVER" "Calling solver %s with criteria %s"
    (OpamCudfSolver.get_name (module S)) criteria;
  let (preamble', u) = S.call ~criteria ?timeout:(!r.solver_timeout) cudf in
  begin match OpamStd.Env.getopt "OPAMCUDFSCORE" with
    | None -> ()
    | Some score_file ->
      let score = solution_score criteria preamble request universe_before u in
      let cout = open_out score_file in
      List.iter (Printf.fprintf cout "%d ") score;
      Printf.fprintf cout "\n";
      close_out cout
  end;
  (preamble', u)
