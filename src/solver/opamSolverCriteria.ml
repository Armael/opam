type filter = Installed | Changed | Removed | New | Upgraded | Downgraded | Requested
type property = string option
type sign = Plus | Minus

type criterion = sign * filter * property
type t = criterion list

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

let of_string s =
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
