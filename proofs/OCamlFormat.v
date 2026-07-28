From Stdlib Require Import Numbers.DecimalString Numbers.HexadecimalString.
Require Import RocqOfOCaml.Libraries.
Require Import RocqOfOCaml.Basics.

Local Open Scope Z_scope.
Local Open Scope string_scope.

(** A constructive interpreter for the statically typed fragment of OCaml's
    [Format] API used by translated programs.

    rocq-of-ocaml erases the indices of OCaml's format GADT in
    [format6_gadt].  The expected Gallina result type still determines the
    sequence of arguments, so [Sprintf] and [Printf] recover that sequence
    through typeclass resolution.  Each instance consumes one conversion from
    the syntax tree.  This avoids the former inconsistent
    [forall A : Set, A] formatting parameters. *)

Definition append := Strings.String.append.

Definition decimal_string (value : Z) : string :=
  DecimalString.NilZero.string_of_int (Z.to_int value).

Definition hexadecimal_string (value : Z) : string :=
  HexadecimalString.NilZero.string_of_int (Z.to_hex_int value).

Fixpoint repeat_ascii (count : nat) (character : ascii) : string :=
  match count with
  | O => ""
  | S count => String character (repeat_ascii count character)
  end.

Definition pad_left
    (padding : CamlinternalFormatBasics.padding_gadt) (value : string) :
    string :=
  match padding with
  | CamlinternalFormatBasics.Lit_padding_gadt
      CamlinternalFormatBasics.Zeros width =>
      append
        (repeat_ascii
          (Nat.sub (Z.to_nat width) (Strings.String.length value))
          "0"%char)
        value
  | _ => value
  end.

Definition render_integer
    (conversion : CamlinternalFormatBasics.int_conv)
    (padding : CamlinternalFormatBasics.padding_gadt)
    (value : Z) : string :=
  pad_left padding
    match conversion with
    | CamlinternalFormatBasics.Int_x
    | CamlinternalFormatBasics.Int_Cx
    | CamlinternalFormatBasics.Int_X
    | CamlinternalFormatBasics.Int_CX => hexadecimal_string value
    | _ => decimal_string value
    end.

Definition render_formatting_literal
    (literal : CamlinternalFormatBasics.formatting_lit) : string :=
  match literal with
  | CamlinternalFormatBasics.Break contents _ _ => contents
  | CamlinternalFormatBasics.Force_newline
  | CamlinternalFormatBasics.Flush_newline => String "010"%char ""
  | CamlinternalFormatBasics.Escaped_at => "@"
  | CamlinternalFormatBasics.Escaped_percent => "%"
  | _ => ""
  end.

Fixpoint render_literals
    (format : CamlinternalFormatBasics.fmt_gadt) : string :=
  match format with
  | CamlinternalFormatBasics.String_literal_gadt literal rest =>
      append literal (render_literals rest)
  | CamlinternalFormatBasics.Char_literal_gadt literal rest =>
      String literal (render_literals rest)
  | CamlinternalFormatBasics.Formatting_lit_gadt literal rest =>
      append (render_formatting_literal literal) (render_literals rest)
  | CamlinternalFormatBasics.Flush_gadt rest => render_literals rest
  | _ => ""
  end.

Class Sprintf (A : Set) := {
  sprintf_from : string -> CamlinternalFormatBasics.fmt_gadt -> A;
}.

Global Instance sprintf_result : Sprintf string := {
  sprintf_from prefix format := append prefix (render_literals format);
}.

Fixpoint sprintf_string_argument {A : Set} `{Sprintf A}
    (prefix : string) (format : CamlinternalFormatBasics.fmt_gadt)
    (value : string) : A :=
  match format with
  | CamlinternalFormatBasics.String_gadt _ rest
  | CamlinternalFormatBasics.Caml_string_gadt _ rest =>
      sprintf_from (append prefix value) rest
  | CamlinternalFormatBasics.String_literal_gadt literal rest =>
      sprintf_string_argument (append prefix literal) rest value
  | CamlinternalFormatBasics.Char_literal_gadt literal rest =>
      sprintf_string_argument (append prefix (String literal "")) rest value
  | CamlinternalFormatBasics.Formatting_lit_gadt literal rest =>
      sprintf_string_argument
        (append prefix (render_formatting_literal literal)) rest value
  | CamlinternalFormatBasics.Flush_gadt rest =>
      sprintf_string_argument prefix rest value
  | _ => sprintf_from prefix CamlinternalFormatBasics.End_of_format_gadt
  end.

Global Instance sprintf_string {A : Set} `{Sprintf A} :
    Sprintf (string -> A) := {
  sprintf_from prefix format := sprintf_string_argument prefix format;
}.

Fixpoint sprintf_integer_argument {A : Set} `{Sprintf A}
    (prefix : string) (format : CamlinternalFormatBasics.fmt_gadt)
    (value : Z) : A :=
  match format with
  | CamlinternalFormatBasics.Int_gadt conversion padding _ rest
  | CamlinternalFormatBasics.Int32_gadt conversion padding _ rest
  | CamlinternalFormatBasics.Nativeint_gadt conversion padding _ rest
  | CamlinternalFormatBasics.Int64_gadt conversion padding _ rest =>
      sprintf_from
        (append prefix (render_integer conversion padding value)) rest
  | CamlinternalFormatBasics.String_literal_gadt literal rest =>
      sprintf_integer_argument (append prefix literal) rest value
  | CamlinternalFormatBasics.Char_literal_gadt literal rest =>
      sprintf_integer_argument (append prefix (String literal "")) rest value
  | CamlinternalFormatBasics.Formatting_lit_gadt literal rest =>
      sprintf_integer_argument
        (append prefix (render_formatting_literal literal)) rest value
  | CamlinternalFormatBasics.Flush_gadt rest =>
      sprintf_integer_argument prefix rest value
  | _ => sprintf_from prefix CamlinternalFormatBasics.End_of_format_gadt
  end.

Global Instance sprintf_integer {A : Set} `{Sprintf A} :
    Sprintf (Z -> A) := {
  sprintf_from prefix format := sprintf_integer_argument prefix format;
}.

Definition sprintf {A : Set} `{Sprintf A}
    (format : CamlinternalFormatBasics.format6_gadt) : A :=
  match format with
  | CamlinternalFormatBasics.Format_gadt syntax _ => sprintf_from "" syntax
  end.

Class Printf (A : Set) := {
  printf_from : CamlinternalFormatBasics.fmt_gadt -> A;
}.

Global Instance printf_result : Printf unit := {
  printf_from _ := tt;
}.

Fixpoint printf_string_argument {A : Set} `{Printf A}
    (format : CamlinternalFormatBasics.fmt_gadt) (_ : string) : A :=
  match format with
  | CamlinternalFormatBasics.String_gadt _ rest
  | CamlinternalFormatBasics.Caml_string_gadt _ rest => printf_from rest
  | CamlinternalFormatBasics.String_literal_gadt _ rest
  | CamlinternalFormatBasics.Char_literal_gadt _ rest
  | CamlinternalFormatBasics.Formatting_lit_gadt _ rest
  | CamlinternalFormatBasics.Flush_gadt rest =>
      printf_string_argument rest ""
  | _ => printf_from CamlinternalFormatBasics.End_of_format_gadt
  end.

Global Instance printf_string {A : Set} `{Printf A} :
    Printf (string -> A) := {
  printf_from format := printf_string_argument format;
}.

Fixpoint printf_integer_argument {A : Set} `{Printf A}
    (format : CamlinternalFormatBasics.fmt_gadt) (_ : Z) : A :=
  match format with
  | CamlinternalFormatBasics.Int_gadt _ _ _ rest
  | CamlinternalFormatBasics.Int32_gadt _ _ _ rest
  | CamlinternalFormatBasics.Nativeint_gadt _ _ _ rest
  | CamlinternalFormatBasics.Int64_gadt _ _ _ rest => printf_from rest
  | CamlinternalFormatBasics.String_literal_gadt _ rest
  | CamlinternalFormatBasics.Char_literal_gadt _ rest
  | CamlinternalFormatBasics.Formatting_lit_gadt _ rest
  | CamlinternalFormatBasics.Flush_gadt rest =>
      printf_integer_argument rest 0
  | _ => printf_from CamlinternalFormatBasics.End_of_format_gadt
  end.

Global Instance printf_integer {A : Set} `{Printf A} :
    Printf (Z -> A) := {
  printf_from format := printf_integer_argument format;
}.

Definition printf {A : Set} `{Printf A}
    (format : CamlinternalFormatBasics.format6_gadt) : A :=
  match format with
  | CamlinternalFormatBasics.Format_gadt syntax _ => printf_from syntax
  end.

Definition eprintf {A : Set} `{Printf A} :
    CamlinternalFormatBasics.format6_gadt -> A :=
  printf.

Definition print_string (_ : string) : unit := tt.

Definition print_flush (_ : unit) : unit := tt.

Example sprintf_two_strings :
  sprintf
    (CamlinternalFormatBasics.Format
      (CamlinternalFormatBasics.String CamlinternalFormatBasics.No_padding
        (CamlinternalFormatBasics.String CamlinternalFormatBasics.No_padding
          CamlinternalFormatBasics.End_of_format))
      "%s%s")
    "ab" "cd" = "abcd" := eq_refl.

Example sprintf_padded_hex :
  sprintf
    (CamlinternalFormatBasics.Format
      (CamlinternalFormatBasics.Int CamlinternalFormatBasics.Int_x
        (CamlinternalFormatBasics.Lit_padding
          CamlinternalFormatBasics.Zeros 2)
        CamlinternalFormatBasics.No_precision
        CamlinternalFormatBasics.End_of_format)
      "%02x")
    10 = "0a" := eq_refl.
