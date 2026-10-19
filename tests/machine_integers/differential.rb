# Native OCaml is the oracle, not a second implementation of wrapping in Ruby.
# Compile the same wrappers to native code and translate them to Gallina, then
# have Rocq check every expected result. All generated files stay in _build.
require 'fileutils'
require 'open3'

root = File.expand_path('../..', __dir__)
runtime = File.expand_path(ENV.fetch('INTEGER_RUNTIME', File.join(root, 'proofs')))
directory = File.join(root, '_build', 'machine-integer-differential')
FileUtils.mkdir_p(directory)
translator = File.join(root, '_build/default/src/rocqOfOCaml.exe')
declarations = []
cases = []

def run!(*command, directory:)
  stdout, stderr, status = Open3.capture3(*command, chdir: directory)
  raise "#{command.join(' ')}\n#{stdout}\n#{stderr}" unless status.success?
  stdout
end

# [native, Gallina] spelling of one argument. Fixed-width suffixes belong only
# to OCaml syntax; the translated carrier remains Z.
def number(value, suffix = '')
  ["(#{value}#{suffix})", "(#{value})"]
end

def text_argument(value)
  [value.dump, '"' + value.gsub('"', '""') + '"']
end

def add_function(declarations, cases, name, parameters, body, result, inputs)
  declarations << "let #{name} #{parameters} = #{body}"
  inputs.each { |args| cases << [name, args, result] }
end

rng = Random.new(755)
[
  ['i', 'Int', 'int', '', 63],
  ['i32', 'Int32', 'int32', 'l', 32],
  ['i64', 'Int64', 'int64', 'L', 64],
  ['native', 'Nativeint', 'nativeint', 'n', 64]
].each do |prefix, mod, type, suffix, width|
  half = 1 << (width - 1)
  edges = [-half, -half + 1, -65537, -2, -1, 0, 1, 2, 65537, half - 2, half - 1]
  pairs = edges.product(edges) + Array.new(40) { [rng.rand(-half...half), rng.rand(-half...half)] }
  unary = edges.map { |x| [number(x, suffix)] }
  %w[add sub mul logand logor logxor compare].each do |op|
    result = op == 'compare' ? 'int' : type
    inputs = pairs.map { |x, y| [number(x, suffix), number(y, suffix)] }
    add_function(declarations, cases, "#{prefix}_#{op}", "(x : #{type}) (y : #{type})",
                 "#{mod}.#{op} x y", result, inputs)
  end
  %w[div rem unsigned_div unsigned_rem unsigned_compare].each do |op|
    next if mod == 'Int' && op.start_with?('unsigned_')
    inputs = pairs.reject { |_, y| y == 0 && op != 'unsigned_compare' }
                  .map { |x, y| [number(x, suffix), number(y, suffix)] }
    result = op == 'unsigned_compare' ? 'int' : type
    add_function(declarations, cases, "#{prefix}_#{op}", "(x : #{type}) (y : #{type})",
                 "#{mod}.#{op} x y", result, inputs)
  end
  %w[neg succ pred abs lognot].each do |op|
    add_function(declarations, cases, "#{prefix}_#{op}", "(x : #{type})",
                 "#{mod}.#{op} x", type, unary)
  end
  %w[shift_left shift_right shift_right_logical].each do |op|
    # Int specifies shifts through Sys.int_size inclusive; boxed types require
    # strictly less than their width. Do not claim equivalence for unspecified counts.
    counts = [0, 1, 2, width / 2, width - 2, width - 1]
    counts << width if mod == 'Int'
    inputs = edges.product(counts).map { |x, k| [number(x, suffix), number(k)] }
    add_function(declarations, cases, "#{prefix}_#{op}", "(x : #{type}) (k : int)",
                 "#{mod}.#{op} x k", type, inputs)
  end
  if mod != 'Int'
    add_function(declarations, cases, "#{prefix}_to_int", "(x : #{type})",
                 "#{mod}.to_int x", 'int', unary)
    add_function(declarations, cases, "#{prefix}_unsigned_to_int", "(x : #{type})",
                 "#{mod}.unsigned_to_int x", 'option:int', unary)
    values = [-(1 << 62), -1, 0, 1, (1 << 31), (1 << 62) - 1]
    add_function(declarations, cases, "#{prefix}_of_int", '(x : int)',
                 "#{mod}.of_int x", type, values.map { |x| [number(x)] })
  end
  if width == 64
    add_function(declarations, cases, "#{prefix}_to_int32", "(x : #{type})",
                 "#{mod}.to_int32 x", 'int32', unary)
    values = [-(1 << 31), -1, 0, 1, (1 << 31) - 1]
    add_function(declarations, cases, "#{prefix}_of_int32", '(x : int32)',
                 "#{mod}.of_int32 x", type, values.map { |x| [number(x, 'l')] })
  end
  parser = mod == 'Int' ? 'int_of_string_opt' : "#{mod}.of_string_opt"
  strings = ['', '+', '-', '-+1', ' 1', '1 ', '_1', '0x', '0x_f', '0b2',
             '1__', '0Xf__f', '-0o77', '+0b11', '0U42', '0u-1']
  [-half - 1, -half, -half + 1, half - 1, half, 2 * half - 1, 2 * half].each do |n|
    strings << n.to_s
  end
  [half - 1, half, 2 * half - 1, 2 * half].each do |n|
    [2, 8, 16].zip(%w[b o x]).each do |base, tag|
      ['', '-', '+'].each { |sign| strings << "#{sign}0#{tag}#{n.to_s(base)}" }
    end
    strings << "0u#{n}"
  end
  add_function(declarations, cases, "#{prefix}_parse", '(s : string)',
               "#{parser} s", "option:#{type}", strings.map { |s| [text_argument(s)] })
  # These constants exercise the translator's literal importer, including bit
  # patterns outside the host tagged-int range and patterns in match branches.
  add_function(declarations, cases, "#{prefix}_literal", '(u : unit)',
               "#{half - 1}#{suffix}", type, [[['()', 'tt']]])
  add_function(declarations, cases, "#{prefix}_pattern", "(x : #{type})",
               "match x with #{-half}#{suffix} -> 1 | #{half - 1}#{suffix} -> 2 | _ -> 3",
               'int', unary)
end

# Stdlib operators, qualified calls, first-class aliases, and intermediate
# overflow affecting control flow must go through the same machine operations.
operators = {'plus' => '+', 'minus' => '-', 'times' => '*', 'divide' => '/',
             'remainder' => 'mod', 'and' => 'land', 'or' => 'lor', 'xor' => 'lxor'}
int_edges = [-(1 << 62), -7, -1, 0, 1, 2, (1 << 62) - 1]
operators.each do |name, op|
  pairs = int_edges.product(int_edges).reject { |_, y| %w[/ mod].include?(op) && y == 0 }
  add_function(declarations, cases, "operator_#{name}", '(x : int) (y : int)',
               "x #{op} y", 'int', pairs.map { |x, y| [number(x), number(y)] })
end
{'neg' => '-x', 'positive' => '+x', 'succ' => 'succ x', 'pred' => 'pred x',
 'abs' => 'abs x', 'not' => 'lnot x'}.each do |name, body|
  add_function(declarations, cases, "operator_#{name}", '(x : int)', body, 'int',
               int_edges.map { |x| [number(x)] })
end
{'left' => 'lsl', 'logical' => 'lsr', 'arithmetic' => 'asr'}.each do |name, op|
  inputs = int_edges.product([0, 1, 31, 62, 63]).map { |x, k| [number(x), number(k)] }
  add_function(declarations, cases, "operator_#{name}", '(x : int) (k : int)',
               "x #{op} k", 'int', inputs)
end
add_function(declarations, cases, 'aliased_add', '(x : int) (y : int)',
             'let f = ( + ) in f x y', 'int', [[number((1 << 62) - 1), number(1)]])
add_function(declarations, cases, 'aliased_div', '(x : int) (y : int)',
             'let f = ( / ) in f x y', 'int', [[number(-(1 << 62)), number(-1)]])
add_function(declarations, cases, 'intermediate_overflow', '(x : int)',
             'if x + 1 < x then 42 else 7', 'int', [[number((1 << 62) - 1)]])
add_function(declarations, cases, 'limits', '(u : unit)',
             'if succ max_int = min_int then Sys.int_size + Sys.word_size else 0',
             'int', [[['()', 'tt']]])
add_function(declarations, cases, 'native_to_int64_literal', '(u : unit)',
             'Int64.of_nativeint (-9223372036854775808n)', 'int64', [[['()', 'tt']]])
add_function(declarations, cases, 'int64_native', '(x : int64)',
             'Int64.to_nativeint x', 'nativeint', [[number(-(1 << 63), 'L')]])
add_function(declarations, cases, 'big_zarith', '(u : unit)',
             'Z.(shift_left one 256 + one)', 'Z.t', [[['()', 'tt']]])
add_function(declarations, cases, 'checked_zarith_conversion', '(u : unit)',
             'Z.to_int (Z.of_int 42)', 'int', [[['()', 'tt']]])
add_function(declarations, cases, 'parse_exn', '(s : string)',
             'int_of_string s', 'int', %w[0 42 -42 0x7fffffffffffffff].map { |s| [text_argument(s)] })
%w[Int32 Int64 Nativeint].each do |mod|
  type = mod.downcase
  add_function(declarations, cases, "#{type}_parse_exn", '(s : string)',
               "#{mod}.of_string s", type, %w[0 42 -42 0xffff].map { |s| [text_argument(s)] })
end
add_function(declarations, cases, 'finite_range_sum', '(count : int) (start : int)',
             'Seq.fold_left ( + ) 0 (Seq.take count (Seq.ints start))', 'int',
             [0, 1, 2, 3, 8].product(int_edges).map { |n, x| [number(n), number(x)] })

zarith = run!('ocamlfind', 'query', 'zarith', directory: directory).strip
File.write(File.join(directory, '.merlin'), "B #{zarith}\n")
# The small merlin-lib installation need not include dot-merlin-reader.
# Put the real interface in the default search directory as well.
FileUtils.cp(File.join(zarith, 'z.cmi'), directory)
File.write(File.join(directory, 'Fixture.ml'), declarations.join("\n") + "\n")
printers = {'int' => 'string_of_int', 'int32' => 'Int32.to_string',
            'int64' => 'Int64.to_string', 'nativeint' => 'Nativeint.to_string', 'Z.t' => 'Z.to_string'}
oracle = cases.map do |name, args, result|
  call = "Fixture.#{name} #{args.map(&:first).join(' ')}"
  if result.start_with?('option:')
    printer = printers.fetch(result.delete_prefix('option:'))
    "print_endline (match #{call} with None -> \"None\" | Some x -> \"Some \" ^ #{printer} x);"
  else
    "print_endline (#{printers.fetch(result)} (#{call}));"
  end
end
File.write(File.join(directory, 'Oracle.ml'), "let () = assert (Sys.int_size = 63);\n" + oracle.join("\n") + "\n()\n")
run!('ocamlfind', 'ocamlopt', '-package', 'zarith', '-linkpkg', '-o', 'oracle',
     'Fixture.ml', 'Oracle.ml', directory: directory)
expected = run!(File.join(directory, 'oracle'), directory: directory).lines.map(&:strip)
raise 'oracle result count mismatch' unless expected.length == cases.length
run!(translator, '-output', 'Fixture.v', 'Fixture.ml', directory: directory)
flags = ['-R', runtime, 'RocqOfOCaml', '-R', directory, 'IntegerTests']
flags << '-impredicative-set' unless ENV['PREDICATIVE'] == '1'
run!('rocq', 'c', *flags, 'Fixture.v', directory: directory)
checks = cases.zip(expected).map do |(name, args, result), value|
  call = "Fixture.#{name} #{args.map(&:last).join(' ')}"
  if result.start_with?('option:')
    want = value == 'None' ? 'None' : "Some (#{value.delete_prefix('Some ')})"
    "(match #{call}, #{want} with Some x, Some y => Z.eqb x y | None, None => true | _, _ => false end)"
  else
    "(Z.eqb (#{call}) (#{Integer(value)}))"
  end
end
header = <<~COQ
  Require Import RocqOfOCaml.RocqOfOCaml IntegerTests.Fixture.
  Import ListNotations.
  Open Scope Z_scope.
  (* A concrete inhabitant for the existing exception boundary, not an axiom.
     Native cases above return normally, so this value must not be observed. *)
  #[local] Instance exceptional_int : Unreachable Z := {| unreachable := 1234567 |}.
  #[local] Instance exceptional_seq : Unreachable (OCamlSeq.t int) :=
    {| unreachable := OCamlSeq.Empty |}.
  #[local] Instance exceptional_node : Unreachable (unit -> OCamlSeq.node int) :=
    {| unreachable := fun _ => OCamlSeq.Nil |}.
COQ
proofs = checks.each_slice(100).with_index.map do |chunk, i|
  "Example batch_#{i} : [#{chunk.join(";\n")}] = List.repeat true #{chunk.length}.\n" \
    "Proof. vm_compute. reflexivity. Qed.\n"
end
File.write(File.join(directory, 'Check.v'), header + proofs.join("\n"))
run!('rocq', 'c', *flags, 'Check.v', directory: directory)
puts "Machine-integer differential tests: #{cases.length} native/translated results agree."
