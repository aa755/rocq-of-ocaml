# Test the actual translated wrappers against the installed OCaml libraries.
require 'fileutils'
require 'open3'

root = File.expand_path('../..', __dir__)
runtime = File.expand_path(ENV.fetch('RUNTIME', File.join(root, 'proofs')))
directory = File.join(root, '_build', 'runtime-differential')
FileUtils.mkdir_p(directory)

def run!(*command, directory:)
  out, err, status = Open3.capture3(*command, chdir: directory)
  raise "#{command.join(' ')}\n#{out}\n#{err}" unless status.success?
  out
end

def number(n)
  ["(#{n})", "(#{n})"]
end

def text(s)
  [s.dump, '"' + s.gsub('"', '""') + '"']
end

declarations = ['module M = Map.Make(Int)']
cases = []
add = lambda do |name, parameters, body, result, inputs|
  declarations << "let #{name} #{parameters} = #{body}"
  inputs.each { |args| cases << [name, args, result] }
end

edges = [-101, -5, -2, -1, 0, 1, 2, 5, 101]
add.call('erem', '(x : Z.t) (m : Z.t)', 'Z.erem x m', 'z',
         edges.product(edges).map { |x, m| [text(x.to_s), text(m.to_s)] }.map do |args|
           args.map { |native, gallina| ["(Z.of_string #{native})", "(OCamlZ.of_string #{gallina})"] }
         end)
zarg = ->(n) { ["(Z.of_string #{n.to_s.dump})", "(#{n})"] }
add.call('powm', '(x : Z.t) (e : Z.t) (m : Z.t)', 'Z.powm x e m', 'z',
         edges.product([-7, -2, -1, 0, 1, 2, 17], edges).map { |row| row.map(&zarg) })
strings = ['', '+', '-', '-+', '+0x10', '-0', '_1', '0x_f', '0b2', '0o8',
           '0u42', ' 1', '1 ', '1__', '0Xf__f', '-+0xF', '0x', '+0b11',
           '-0o77', '--1', '++1', '123456789012345678901234567890']
add.call('parse', '(s : string)', 'Z.of_string s', 'z', strings.map { |s| [text(s)] })

hash_rng = Random.new(755)
wide_edges = [0, 1, 42, 255, 256] + [8, 31, 32, 62, 63, 64, 65, 127, 128, 255, 256, 300].flat_map do |bits|
  [-1, 0, 1].map { |delta| 2**bits + delta }
end
wide_edges += Array.new(50) { hash_rng.rand(0...2**512) }
wide_edges = (wide_edges + wide_edges.map { |x| -x }).uniq
add.call('to_bits', '(x : Z.t)', 'Z.to_bits x', 'string_bytes',
         wide_edges.map { |x| [zarg.call(x)] })
add.call('z_hash', '(x : Z.t)', 'Z.hash x', 'int',
         wide_edges.map { |x| [zarg.call(x)] })
seeds = [-(2**62), -4294967297, -1, 0, 1, 42, 2**32, 2**62 - 1]
add.call('z_seeded_hash', '(seed : int) (x : Z.t)', 'Z.seeded_hash seed x', 'int',
         seeds.product(wide_edges).map { |seed, x| [number(seed), zarg.call(x)] })
int64_edges = wide_edges.select { |x| -(2**63) <= x && x < 2**63 }
int64_edges += Array.new(100) { hash_rng.rand(-(2**63)...2**63) }
i64arg = ->(n) { ["(#{n}L)", "(#{n})"] }
add.call('int64_hash', '(x : int64)', 'Int64.hash x', 'int',
         int64_edges.map { |x| [i64arg.call(x)] })
add.call('int64_seeded_hash', '(seed : int) (x : int64)',
         'Int64.seeded_hash seed x', 'int',
         seeds.product(int64_edges).map { |seed, x| [number(seed), i64arg.call(x)] })
rng = Random.new(755)
maps = [[], [[1, 10], [1, 20]], [[2, 3], [1, 4], [2, 5]],
        [[1, 20], [1, 10]]] + Array.new(30) { Array.new(20) { [rng.rand(-3..3), rng.rand(-30..30)] } }
map_inputs = maps.product((-4..4).to_a).map do |pairs, key|
  bindings = '[' + pairs.map { |x, y| "(#{x}, #{y})" }.join('; ') + ']'
  [[bindings, bindings], number(key)]
end
add.call('map_lookup', '(xs : (int * int) list) (k : int)',
         'M.find_opt k (M.of_list xs)', 'option', map_inputs)
lists = [[], [3, 1, 2, 1], [-1, 0, 1], [9, 8, 7, 6]] +
        Array.new(30) { Array.new(15) { rng.rand(-50..50) } }
list_inputs = lists.map do |xs|
  value = '[' + xs.map { |x| "(#{x})" }.join('; ') + ']'
  [[value, value]]
end
add.call('sort', '(xs : int list)', 'List.sort Int.compare xs', 'list', list_inputs)
add.call('sort_uniq', '(xs : int list)', 'List.sort_uniq Int.compare xs', 'list', list_inputs)
add.call('take', '(n : int)', 'List.of_seq (Seq.take n (List.to_seq [3; 1; 2; 1]))',
         'list', (0..7).map { |n| [number(n)] })
add.call('drop', '(n : int)', 'List.of_seq (Seq.drop n (List.to_seq [3; 1; 2; 1]))',
         'list', (0..7).map { |n| [number(n)] })
add.call('list_init', '(n : int)', 'List.init n (fun i -> i * 3)',
         'list', (0..20).map { |n| [number(n)] })
add.call('init_buffer', '(n : int)', 'Bigstring.init n (fun i -> Char.chr (i mod 256))',
         'bytes', [0, 1, 2, 31, 32, 255, 256, 257].map { |n| [number(n)] })
%w[int32 int64 nativeint string].each do |type|
  values = type == 'string' ? ['', 'a', 'b', 'aa', 'z'].map { |x| text(x) } :
    [-2147483648, -1, 0, 1, 2147483647].map do |x|
      suffix = {'int32' => 'l', 'int64' => 'L', 'nativeint' => 'n'}.fetch(type)
      ["(#{x}#{suffix})", "(#{x})"]
    end
  {'lt' => '<', 'le' => '<=', 'gt' => '>', 'ge' => '>='}.each do |name, op|
    add.call("#{type}_#{name}", "(x : #{type}) (y : #{type})",
             "if x #{op} y then 1 else 0", 'int', values.product(values))
  end
  add.call("#{type}_compare", "(x : #{type}) (y : #{type})",
           'Stdlib.compare x y', 'int', values.product(values))
end

%w[zarith bigstring].each do |package|
  path = run!('ocamlfind', 'query', package, directory: directory).strip
  Dir.glob(File.join(path, '*.cmi')).each { |file| FileUtils.cp(file, directory) }
end
File.write(File.join(directory, 'Fixture.ml'), declarations.join("\n") + "\n")
printers = {'z' => 'Z.to_string', 'int' => 'string_of_int',
            'string_bytes' => '(fun x -> show_list (List.init (String.length x) (fun i -> Char.code x.[i])))',
            'list' => 'show_list', 'bytes' => '(fun x -> show_list (List.init (Bigstring.length x) (fun i -> Char.code (Bigstring.get x i))))',
            'option' => '(function None -> "None" | Some x -> "Some " ^ string_of_int x)'}
oracle = cases.map do |name, args, result|
  call = "Fixture.#{name} #{args.map(&:first).join(' ')}"
  "print_endline (try #{printers.fetch(result)} (#{call}) with Division_by_zero | Invalid_argument _ -> \"Error\");"
end
File.write(File.join(directory, 'Oracle.ml'), <<~ML + oracle.join("\n") + "\n()\n")
  let show_list xs = String.concat ";" (List.map string_of_int xs)
  let () =
ML
run!('ocamlfind', 'ocamlopt', '-package', 'zarith,bigstring', '-linkpkg',
     '-o', 'oracle', 'Fixture.ml', 'Oracle.ml', directory: directory)
expected = run!(File.join(directory, 'oracle'), directory: directory).lines.map(&:strip)
raise 'oracle result count mismatch' unless expected.length == cases.length
run!(File.join(root, '_build/default/src/rocqOfOCaml.exe'), '-output', 'Fixture.v',
     'Fixture.ml', directory: directory)
flags = ['-R', runtime, 'RocqOfOCaml', '-R', directory, 'RuntimeTests']
flags << '-impredicative-set' unless ENV['PREDICATIVE'] == '1'
run!('rocq', 'c', *flags, 'Fixture.v', directory: directory)
checks = cases.zip(expected).map do |(name, args, result), value|
  call = "Fixture.#{name} #{args.map(&:last).join(' ')}"
  want = case result
         when 'z', 'int' then value == 'Error' ? '1234567' : "(#{Integer(value)})"
         when 'option' then value == 'None' ? 'None' : "Some (#{Integer(value.delete_prefix('Some '))})"
         when 'list', 'bytes', 'string_bytes'
           nums = value.empty? ? [] : value.split(';').map { |x| Integer(x) }
           list = '[' + nums.map { |x| "(#{x})" }.join('; ') + ']'
           result == 'list' ? list : "string_of_list_ascii (List.map (fun z => ascii_of_N (Z.to_N z)) #{list})"
         end
  "(equiv_decb (#{call}) (#{want}))"
end
header = <<~COQ
  Require Import RocqOfOCaml.RocqOfOCaml RuntimeTests.Fixture.
  Import ListNotations.
  Open Scope Z_scope.
  #[local] Instance fallback_int : Unreachable Z := {| unreachable := 1234567 |}.
  #[local] Instance fallback_bytes : Unreachable string := {| unreachable := EmptyString |}.
  #[local] Instance fallback_ascii : Unreachable ascii := {| unreachable := ascii_of_nat 0 |}.
  #[local] Instance fallback_list : Unreachable (list int) := {| unreachable := [] |}.
  #[local] Instance fallback_seq : Unreachable (OCamlSeq.t int) := {| unreachable := OCamlSeq.Empty |}.
  #[local] Instance fallback_node : Unreachable (unit -> OCamlSeq.node int) := {| unreachable := fun _ => OCamlSeq.Nil |}.
COQ
proofs = checks.each_slice(50).with_index.map do |chunk, i|
  "Example batch_#{i} : [#{chunk.join(";\n")}] = List.repeat true #{chunk.length}.\n" \
    "Proof. vm_compute. reflexivity. Qed.\n"
end
File.write(File.join(directory, 'Check.v'), header + proofs.join("\n"))
run!('rocq', 'c', *flags, 'Check.v', directory: directory)
puts "Runtime differential tests: #{cases.length} native/translated results agree."
