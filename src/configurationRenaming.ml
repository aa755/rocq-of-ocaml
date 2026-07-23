let rules =
  [
    (* Standard-library modules represented by rocq-of-ocaml's executable
       Gallina compatibility layer.  The wildcard rules rewrite descendants;
       the exact rules rewrite module expressions such as [include Map]. *)
    ("Stdlib.Map", "RocqOfOCaml.OCamlMap");
    ("Stdlib.Map.*", "RocqOfOCaml.OCamlMap");
    ("Stdlib.Option", "RocqOfOCaml.OCamlOption");
    ("Stdlib.Option.*", "RocqOfOCaml.OCamlOption");
    ("Stdlib._Set", "RocqOfOCaml.OCamlSet");
    ("Stdlib._Set.*", "RocqOfOCaml.OCamlSet");
    ("Stdlib.List", "RocqOfOCaml.OCamlList");
    ("Stdlib.List.*", "RocqOfOCaml.OCamlList");
    ("Stdlib.Seq", "RocqOfOCaml.OCamlSeq");
    ("Stdlib.Seq.*", "RocqOfOCaml.OCamlSeq");
    ("Stdlib.String", "RocqOfOCaml.OCamlString");
    ("Stdlib.String.*", "RocqOfOCaml.OCamlString");
    ("Stdlib.Uchar", "RocqOfOCaml.OCamlUchar");
    ("Stdlib.Uchar.*", "RocqOfOCaml.OCamlUchar");
    ("Stdlib.Char", "RocqOfOCaml.OCamlChar");
    ("Stdlib.Char.*", "RocqOfOCaml.OCamlChar");
    ("Stdlib.Format", "RocqOfOCaml.OCamlFormat");
    ("Stdlib.Format.*", "RocqOfOCaml.OCamlFormat");
    ("Stdlib.Fun", "RocqOfOCaml.OCamlFun");
    ("Stdlib.Fun.*", "RocqOfOCaml.OCamlFun");
    ("Stdlib.Hashtbl", "RocqOfOCaml.OCamlHashtbl");
    ("Stdlib.Hashtbl.*", "RocqOfOCaml.OCamlHashtbl");
    ("Stdlib.Iarray", "RocqOfOCaml.OCamlIarray");
    ("Stdlib.Iarray.*", "RocqOfOCaml.OCamlIarray");
    ("Stdlib.Int", "RocqOfOCaml.OCamlInt");
    ("Stdlib.Int.*", "RocqOfOCaml.OCamlInt");
    ("Stdlib.Int32", "RocqOfOCaml.OCamlInt32");
    ("Stdlib.Int32.*", "RocqOfOCaml.OCamlInt32");
    ("Stdlib.Int64", "RocqOfOCaml.OCamlInt64");
    ("Stdlib.Int64.*", "RocqOfOCaml.OCamlInt64");
    ("Stdlib.Result", "RocqOfOCaml.OCamlResult");
    ("Stdlib.Result.*", "RocqOfOCaml.OCamlResult");
    ("Stdlib.Bigarray", "RocqOfOCaml.OCamlBigarray");
    ("Stdlib.Bigarray.*", "RocqOfOCaml.OCamlBigarray");
    ("Yojson.Safe", "RocqOfOCaml.OCamlYojson");
    ("Yojson.Safe.*", "RocqOfOCaml.OCamlYojson");
    (* Built-in types *)
    ("char", "ascii");
    ("()", "tt");
    ("op_coloncolon", "Datatypes.cons");
    ("Ok", "inl");
    ("Error", "inr");
    ("Stdlib.Ok", "inl");
    ("Stdlib.Error", "inr");
    ("Stdlib.Result.ok", "inl");
    ("Stdlib.Result.error", "inr");
    ("Stdlib.Result._error", "inr");
    ("exn", "extensible_type");
    (* Predefined exceptions *)
    ("Match_failure", "RocqOfOCaml.Match_failure");
    ("Assert_failure", "RocqOfOCaml.Assert_failure");
    ("Invalid_argument", "RocqOfOCaml.Invalid_argument");
    ("Failure", "RocqOfOCaml.Failure");
    ("Not_found", "RocqOfOCaml.Not_found");
    ("Out_of_memory", "RocqOfOCaml.Out_of_memory");
    ("Stack_overflow", "RocqOfOCaml.Stack_overflow");
    ("Sys_error", "RocqOfOCaml.Sys_error");
    ("End_of_file", "RocqOfOCaml.End_of_file");
    ("Division_by_zero", "RocqOfOCaml.Division_by_zero");
    ("Sys_blocked_io", "RocqOfOCaml.Sys_blocked_io");
    ("Undefined_recursive_module", "RocqOfOCaml.Undefined_recursive_module");
    (* Optional parameters *)
    ("*predef*.None", "None");
    ("*predef*.Some", "Some");
    (* Stdlib *)
    (* Exceptions *)
    ("Stdlib.invalid_arg", "RocqOfOCaml.Basics.Stdlib.invalid_arg");
    ("Stdlib.failwith", "RocqOfOCaml.Basics.Stdlib.failwith");
    ("Stdlib.raise", "RocqOfOCaml.Basics.Stdlib.raise");
    ("Stdlib.Exit", "RocqOfOCaml.Basics.Stdlib.Exit");
    (* Comparisons *)
    ("Stdlib.op_eq", "equiv_decb");
    ("Stdlib.op_eqeq", "RocqOfOCaml.Basics.Stdlib.physical_equal");
    ("Stdlib.op_ltgt", "nequiv_decb");
    ("Stdlib.op_lt", "RocqOfOCaml.Basics.Stdlib.lt");
    ("Stdlib.op_gt", "RocqOfOCaml.Basics.Stdlib.gt");
    ("Stdlib.op_lteq", "RocqOfOCaml.Basics.Stdlib.le");
    ("Stdlib.op_gteq", "RocqOfOCaml.Basics.Stdlib.ge");
    ("Stdlib.compare", "RocqOfOCaml.Basics.Stdlib.compare");
    ("Stdlib.min", "RocqOfOCaml.Basics.Stdlib.min");
    ("Stdlib.max", "RocqOfOCaml.Basics.Stdlib.max");
    (* Boolean operations *)
    ("Stdlib.not", "negb");
    ("Stdlib.op_andand", "andb");
    ("Stdlib.op_and", "andb");
    ("Stdlib.op_pipepipe", "orb");
    ("Stdlib.or", "orb");
    (* Integer arithmetic *)
    ("Stdlib.op_tildeminus", "Z.opp");
    ("Stdlib.op_tildeplus", "");
    ("Stdlib.succ", "Z.succ");
    ("Stdlib.pred", "Z.pred");
    ("Stdlib.op_plus", "Z.add");
    ("Stdlib.op_minus", "Z.sub");
    ("Stdlib.op_star", "Z.mul");
    ("Stdlib.op_div", "Z.quot");
    ("Stdlib._mod", "Z.rem");
    ("Stdlib.abs", "Z.abs");
    (* Bitwise operations *)
    ("Stdlib.land", "Z.land");
    ("Stdlib.lor", "Z.lor");
    ("Stdlib.lxor", "Z.lxor");
    ("Stdlib.lsl", "Z.shiftl");
    ("Stdlib.lsr", "Z.shiftr");
    ("Stdlib.asr", "Z.shiftr");
    (* Floating-point arithmetic *)
    (* String operations *)
    ("Stdlib.op_caret", "String.append");
    (* Character operations *)
    ("Stdlib.int_of_char", "RocqOfOCaml.Basics.Stdlib.int_of_char");
    ("Stdlib.char_of_int", "RocqOfOCaml.Basics.Stdlib.char_of_int");
    (* Unit operations *)
    ("Stdlib.ignore", "RocqOfOCaml.Basics.Stdlib.ignore");
    (* String conversion functions *)
    ("Stdlib.string_of_bool", "RocqOfOCaml.Basics.Stdlib.string_of_bool");
    ("Stdlib.bool_of_string", "RocqOfOCaml.Basics.Stdlib.bool_of_string");
    ("Stdlib.string_of_int", "RocqOfOCaml.Basics.Stdlib.string_of_int");
    ("Stdlib.int_of_string", "RocqOfOCaml.Basics.Stdlib.int_of_string");
    (* Pair operations *)
    ("Stdlib.fst", "fst");
    ("Stdlib.snd", "snd");
    (* List operations *)
    ("Stdlib.op_at", "RocqOfOCaml.Basics.Stdlib.app");
    (* Mutable runtime cells.  Their Gallina compatibility definitions make
       the unsupported effect boundary explicit. *)
    ("Stdlib.Lazy.t", "RocqOfOCaml.Basics.Stdlib.Lazy.t");
    ("Stdlib.Lazy.from_fun", "RocqOfOCaml.Basics.Stdlib.Lazy.from_fun");
    ("Stdlib.Lazy.force", "RocqOfOCaml.Basics.Stdlib.Lazy.force");
    ("Stdlib.Atomic.make", "RocqOfOCaml.Basics.Stdlib.Atomic.make");
    ("Stdlib.Atomic.exchange", "RocqOfOCaml.Basics.Stdlib.Atomic.exchange");
    ("Stdlib.ref_value", "RocqOfOCaml.Basics.Stdlib.ref_value");
    ("Stdlib.op_exclamation", "RocqOfOCaml.Basics.Stdlib.op_exclamation");
    ("Stdlib.op_coloneq", "RocqOfOCaml.Basics.Stdlib.op_coloneq");
    (* Input/output *)
    (* Output functions on standard output *)
    ("Stdlib.print_char", "RocqOfOCaml.Basics.Stdlib.print_char");
    ("Stdlib.print_string", "RocqOfOCaml.Basics.Stdlib.print_string");
    ("Stdlib.print_int", "RocqOfOCaml.Basics.Stdlib.print_int");
    ("Stdlib.print_endline", "RocqOfOCaml.Basics.Stdlib.print_endline");
    ("Stdlib.print_newline", "RocqOfOCaml.Basics.Stdlib.print_newline");
    (* Output functions on standard error *)
    ("Stdlib.prerr_char", "RocqOfOCaml.Basics.Stdlib.prerr_char");
    ("Stdlib.prerr_string", "RocqOfOCaml.Basics.Stdlib.prerr_string");
    ("Stdlib.prerr_int", "RocqOfOCaml.Basics.Stdlib.prerr_int");
    ("Stdlib.prerr_endline", "RocqOfOCaml.Basics.Stdlib.prerr_endline");
    ("Stdlib.prerr_newline", "RocqOfOCaml.Basics.Stdlib.prerr_newline");
    (* Input functions on standard input *)
    ("Stdlib.read_line", "RocqOfOCaml.Basics.Stdlib.read_line");
    ("Stdlib.read_int", "RocqOfOCaml.Basics.Stdlib.read_int");
    (* General output functions *)
    (* General input functions *)
    (* Operations on large files *)
    (* References *)
    (* Result type *)
    ("Stdlib.result", "sum");
    ("Stdlib.Either.t", "sum");
    ("Stdlib.Either.Left", "inl");
    ("Stdlib.Either.Right", "inr");
    (* Operations on format strings *)
    (* Program termination *)

    (* Bytes *)
    ("Stdlib.Bytes.cat", "String.append");
    ("Stdlib.Bytes.concat", "String.concat");
    ("Stdlib.Bytes.length", "String.length");
    ("Stdlib.Bytes.sub", "String.sub");
    (* List *)
    ("Stdlib.List.exists", "RocqOfOCaml.OCamlList._exists");
    ("Stdlib.List.exists2", "RocqOfOCaml.OCamlList._exists2");
    ("Stdlib.List.length", "RocqOfOCaml.OCamlList.length");
    ("Stdlib.List.map", "RocqOfOCaml.OCamlList.map");
    ("Stdlib.List.rev", "RocqOfOCaml.OCamlList.rev");
    (* Seq *)
    ("Stdlib.Seq.t", "RocqOfOCaml.OCamlSeq.t");
    (* String *)
    ("Stdlib.String.length", "RocqOfOCaml.OCamlString.length");
    (* Zarith operations whose names, interfaces, or semantics differ from
       Rocq's [Z] library. *)
    ("Z.geq", "Z.geb");
    ("Z.leq", "Z.leb");
    ("Z.compare", "RocqOfOCaml.OCamlZ.compare");
    ("Z.equal", "Z.eqb");
    ("Z.logand", "Z.land");
    ("Z.logor", "Z.lor");
    ("Z.logxor", "Z.lxor");
    ("Z.lognot", "Z.lnot");
    ("Z.shift_left", "Z.shiftl");
    ("Z.shift_right", "Z.shiftr");
    ("Z.op_plus", "Z.add");
    ("Z.op_minus", "Z.sub");
    ("Z.op_star", "Z.mul");
    ("Z.op_div", "Z.quot");
    ("Z.op_starstar", "Z.pow");
    ("Z.op_tildedollar", "RocqOfOCaml.OCamlZ.op_tildedollar");
    ("Z.div_rem", "Z.quotrem");
    ("Z.of_int", "RocqOfOCaml.OCamlZ.of_int");
    ("Z.of_int32", "RocqOfOCaml.OCamlZ.of_int32");
    ("Z.of_int64", "RocqOfOCaml.OCamlZ.of_int64");
    ("Z.of_int32_unsigned", "RocqOfOCaml.OCamlZ.of_int32_unsigned");
    ("Z.of_int64_unsigned", "RocqOfOCaml.OCamlZ.of_int64_unsigned");
    ("Z.to_int", "RocqOfOCaml.OCamlZ.to_int");
    ("Z.to_int32", "RocqOfOCaml.OCamlZ.to_int32");
    ("Z.to_int64", "RocqOfOCaml.OCamlZ.to_int64");
    ("Z.to_int32_unsigned", "RocqOfOCaml.OCamlZ.to_int32_unsigned");
    ("Z.to_int64_unsigned", "RocqOfOCaml.OCamlZ.to_int64_unsigned");
    ("Z.fits_int", "RocqOfOCaml.OCamlZ.fits_int");
    ("Z.numbits", "RocqOfOCaml.OCamlZ.numbits");
    ("Z.extract", "RocqOfOCaml.OCamlZ.extract");
    ("Z.signed_extract", "RocqOfOCaml.OCamlZ.signed_extract");
    ("Z.to_bits", "RocqOfOCaml.OCamlZ.to_bits");
    ("Z.of_bits", "RocqOfOCaml.OCamlZ.of_bits");
    ("Z.powm", "RocqOfOCaml.OCamlZ.powm");
    ("Z.hash", "RocqOfOCaml.OCamlZ.hash");
    ("Z.to_string", "RocqOfOCaml.OCamlZ.to_string");
    ("Z.of_string", "RocqOfOCaml.OCamlZ.of_string");
    ("Z.format", "RocqOfOCaml.OCamlZ.format");
  ]
