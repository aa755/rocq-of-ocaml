# Exercise the fail-closed comparison policy without relying on output snapshots.
require 'fileutils'
require 'json'
require 'open3'
require 'tmpdir'

root = File.expand_path('../..', __dir__)
translator = ENV.fetch('TRANSLATOR', File.join(root, '_build/default/src/rocqOfOCaml.exe'))
cases = {
  'int_equal' => ['let test (x : int) y = x = y', true],
  'int_order' => ['let test (x : int) y = x < y', true],
  'string_order' => ['let test (x : string) y = compare x y', true],
  'list_equal' => ['let test (x : int list) y = x = y', true],
  'nested_equal' => ['let test (x : (char * int option) list) y = x = y', true],
  'array_equal' => ['let test (x : int array) y = x = y', true],
  'explicit_comparator' => ['let test cmp xs = List.sort cmp xs', true],
  'module_alias_concrete' => ['module S = Stdlib\nlet test (x : int) y = S.compare x y', true],
  'poly_equal' => ['let test x y = x = y', false],
  'poly_not_equal' => ['let test x y = x <> y', false],
  'poly_compare' => ['let test x y = compare x y', false],
  'hidden_poly_compare' => ['include struct let test x y = compare x y end [@@merlin.hide]', false],
  'poly_min' => ['let test x y = min x y', false],
  'physical_equal' => ['let test (x : int) y = x == y', false],
  'physical_not_equal' => ['let test (x : int) y = x != y', false],
  'float_equal' => ['let test (x : float) y = x = y', false],
  'nested_float_equal' => ['let test (x : float list) y = x = y', false],
  'constructor_float_equal' => ['let test (x : float option) = x = Some 0.0', false],
  'constructor_int_equal' => ['let test (x : int option) = x = Some 1', true],
  'constructor_none' => ['let test (x : float option) = x = None', true],
  'shadowed_int' => ['type int = A | B\nlet test (x : int) y = x = y', false],
  'value_alias' => ['let comparison = compare\nlet test x y = comparison x y', false],
  'module_alias' => ['module S = Stdlib\nlet test x y = S.compare x y', false],
  'list_mem' => ['let test (x : int) xs = List.mem x xs', false],
  'list_memq' => ['let test x xs = List.memq x xs', false],
  'list_alias' => ['module L = List\nlet test x xs = L.assoc_opt x xs', false],
  'reexport' => ['module M = struct include List let extra = 1 end', false],
  'safe_alias_use' => ['module L = List\nlet test f xs = L.map f xs', true],
  'functor_include' => ['module F (X : sig val x : int end) = struct let y = X.x end\nmodule M = struct include F(struct let x = 1 end) let z = y end\nlet test = M.z', true],
  'primitive_alias' => ['external cmp : \'a -> \'a -> int = "%compare"\nlet test x y = cmp x y', false],
  'primitive_export' => ['external cmp : \'a -> \'a -> int = "%compare"', false]
}

Dir.mktmpdir('strict-comparisons-') do |directory|
  cases.each do |name, (source, accepted)|
    input = File.join(directory, "#{name}.ml")
    output = File.join(directory, "#{name}.v")
    File.write(input, source.gsub('\n', "\n") + "\n")
    stdout, stderr, status = Open3.capture3(
      translator, '--forbid-polymorphic-comparison', '-output', output, input
    )
    if accepted
      raise "#{name}: unexpectedly rejected\n#{stdout}\n#{stderr}" unless status.success? && File.file?(output)
      if ENV['STRICT_COMPARISON_RUNTIME']
        File.open(output, 'a') { |file| file.puts "\nPrint Assumptions test." }
        check, errors, compiled = Open3.capture3(
          'rocq', 'c', '-Q', ENV.fetch('STRICT_COMPARISON_RUNTIME'), 'RocqOfOCaml', output
        )
        unless compiled.success? && check.include?('Closed under the global context')
          raise "#{name}: not kernel-checked and assumption-free\n#{check}\n#{errors}"
        end
      end
    else
      unless !status.success? && !File.exist?(output) &&
             stdout.include?('forbidden_comparison') && stdout.include?('Definition ')
        contents = File.file?(output) ? File.read(output) : ''
        raise "#{name}: did not reject without output\n#{stdout}\n#{stderr}\n#{contents}"
      end
    end
  end

  # Pruning is explicit, not an implicit change to List's behavior.
  input = File.join(directory, 'pruned.ml')
  output = File.join(directory, 'pruned.v')
  config = File.join(directory, 'pruned.json')
  File.write(input, "module M = struct include List let extra = 1 end\nlet test f xs = M.map f xs\n")
  names = %w[mem memq assoc assoc_opt assq assq_opt mem_assoc mem_assq remove_assoc remove_assq]
  File.write(config, JSON.generate({
    forbid_polymorphic_comparison: true,
    excluded_definitions: names.map { |name| ['*', "M.#{name}"] }
  }))
  stdout, stderr, status = Open3.capture3(translator, '-config', config, '-output', output, input)
  raise "explicitly pruned include rejected\n#{stdout}\n#{stderr}" unless status.success? && File.file?(output)

  input = File.join(directory, 'blacklisted.ml')
  output = File.join(directory, 'blacklisted.v')
  config = File.join(directory, 'blacklisted.json')
  File.write(input, "let test x y = x = y\n")
  File.write(output, 'previous output')
  File.write(config, JSON.generate({
    forbid_polymorphic_comparison: true,
    error_category_blacklist: ['forbidden_comparison'],
    error_filename_blacklist: ['*'],
    error_message_blacklist: ['.*']
  }))
  stdout, stderr, status = Open3.capture3(translator, '-config', config, '-output', output, input)
  unless !status.success? && File.read(output) == 'previous output' &&
         stdout.include?('forbidden_comparison')
    raise "blacklists bypassed strict mode\n#{stdout}\n#{stderr}"
  end
end
puts "Strict comparison checks: #{cases.length + 2} passed"
