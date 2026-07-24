type t = {
  ident : Ident.t option;
  module_type : Typedtree.module_type;
  path_aliases : (Ident.t * Path.t) list;
}
