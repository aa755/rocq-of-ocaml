(** OCaml permits different variant types in one module to reuse a constructor
    name, while Rocq puts every inductive constructor in the enclosing module
    namespace.  Assign a deterministic fresh name to each later collision and
    key it by compiler [Uid], which is shared by declarations and uses. *)

module StringSet = Set.Make (String)

type t = string Types.Uid.Map.t

let empty : t = Types.Uid.Map.empty

let find (uid : Types.Uid.t) (names : t) : string option =
  Types.Uid.Map.find_opt uid names

type constructor = {
  owner : string;
  name : string;
  uid : Types.Uid.t;
}

let structure_constructors
    (structure : Typedtree.structure) : constructor list =
  structure.str_items
  |> List.concat_map (fun (item : Typedtree.structure_item) ->
         match item.str_desc with
         | Tstr_type (_, declarations) ->
             declarations
             |> List.concat_map
                  (fun (declaration : Typedtree.type_declaration) ->
                    match declaration.typ_type.type_kind with
                    | Type_variant (constructors, _) ->
                        constructors
                        |> List.map
                             (fun (constructor : Types.constructor_declaration) ->
                               {
                                 owner = Ident.name declaration.typ_id;
                                 name = Ident.name constructor.cd_id;
                                 uid = constructor.cd_uid;
                               })
                    | Type_abstract _
                    | Type_record _
                    | Type_open ->
                        [])
         | _ -> [])

let rec fresh_name (occupied : StringSet.t) (base : string) (index : int) :
    string =
  let candidate =
    if index = 0 then base else base ^ "_" ^ string_of_int (index + 1)
  in
  if StringSet.mem candidate occupied then
    fresh_name occupied base (index + 1)
  else
    candidate

let add_structure (names : t) (structure : Typedtree.structure) : t =
  let constructors = structure_constructors structure in
  let occupied =
    constructors
    |> List.fold_left
         (fun occupied constructor ->
           StringSet.add constructor.name occupied)
         StringSet.empty
  in
  let _, _, names =
    constructors
    |> List.fold_left
         (fun (seen, occupied, names) constructor ->
           if StringSet.mem constructor.name seen then
             let renamed =
               fresh_name occupied
                 (constructor.name ^ "_" ^ constructor.owner)
                 0
             in
             ( seen,
               StringSet.add renamed occupied,
               Types.Uid.Map.add constructor.uid renamed names )
           else
             (StringSet.add constructor.name seen, occupied, names))
         (StringSet.empty, occupied, names)
  in
  names

let of_typedtree (typedtree : Merlin_kernel.Mtyper.typedtree) : t =
  let names = ref empty in
  let open Tast_iterator in
  let iterator =
    {
      default_iterator with
      structure =
        (fun self structure ->
          names := add_structure !names structure;
          default_iterator.structure self structure);
    }
  in
  (match typedtree with
  | `Implementation structure -> iterator.structure iterator structure
  | `Interface signature -> iterator.signature iterator signature);
  !names
