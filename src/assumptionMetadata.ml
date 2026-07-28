type payload = {
  version : int;
  specs : Structure.qualified_assumption_call_specs;
}

let extension = ".rocq-assumptions"
let magic = "rocq-of-ocaml assumption metadata\n"
let version = 1

let write (file_name : string)
    (specs : Structure.qualified_assumption_call_specs) : unit =
  let channel = open_out_bin file_name in
  Fun.protect
    ~finally:(fun () -> close_out channel)
    (fun () ->
      output_string channel magic;
      Marshal.to_channel channel { version; specs } [])

let read (file_name : string) : Structure.qualified_assumption_call_specs =
  let channel = open_in_bin file_name in
  Fun.protect
    ~finally:(fun () -> close_in channel)
    (fun () ->
      let actual_magic = really_input_string channel (String.length magic) in
      if actual_magic <> magic then
        failwith
          (Printf.sprintf
             "Invalid rocq-of-ocaml assumption metadata file '%s'"
             file_name);
      let payload : payload = Marshal.from_channel channel in
      if payload.version <> version then
        failwith
          (Printf.sprintf
             "Unsupported assumption metadata version %d in '%s' (expected \
              %d)"
             payload.version file_name version);
      payload.specs)

let of_directory (directory : string) :
    Structure.qualified_assumption_call_specs =
  if not (Sys.file_exists directory && Sys.is_directory directory) then
    failwith
      (Printf.sprintf
         "Assumption metadata directory '%s' does not exist"
         directory);
  Sys.readdir directory |> Array.to_list |> List.sort String.compare
  |> List.filter (fun name -> Filename.check_suffix name extension)
  |> List.concat_map (fun name -> read (Filename.concat directory name))
