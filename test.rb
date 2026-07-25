# encoding: utf-8
# Run the tests in 'tests/'
require 'fileutils'
require 'open3'
require 'tmpdir'

class Test
  attr_reader :source_file

  def initialize(source_file)
    @source_file = source_file
  end

  def base_name
    File.basename(@source_file, '.*')
  end

  def generated_name
    File.join(File.dirname(@source_file), base_name + '.v')
  end

  def rocq_of_ocaml_cmd(extra_args = [])
    local_executable = '_build/default/src/rocqOfOCaml.exe'
    rocq_of_ocaml =
      ARGV[0] == '--with-coverage' ?
        ['dune', 'exec', '--instrument-with', 'bisect_ppx', 'src/rocqOfOCaml.exe', '--'] :
        [File.executable?(local_executable) ? local_executable : 'rocq-of-ocaml']
    cmd = [*rocq_of_ocaml, '-output', '/dev/stdout']
    configuration_file = File.join(File.dirname(@source_file), base_name + '.json')
    cmd.push('-config', configuration_file) if File.exist?(configuration_file)
    cmd.push(*extra_args)
    cmd.push(@source_file)
  end

  def rocq_of_ocaml
    # We remove the fist line which is a success message
    cmd = rocq_of_ocaml_cmd
    output, error, status = Open3.capture3(*cmd)
    unless status.success?
      warn "Command failed: #{cmd.join(' ')}"
      warn error unless error.empty?
      raise "Command failed"
    end
    output.force_encoding("utf-8").lines.drop(1).join
  end

  def reference
    file_name = generated_name
    FileUtils.touch file_name unless File.exist?(file_name)
    File.read(file_name, :encoding => 'utf-8')
  end

  # Update the reference snapshot file.
  def update
    output = rocq_of_ocaml
    file_name = generated_name
    File.write(file_name, output)
  end

  def check
    update if ENV['UPDATE_SNAPSHOTS'] == '1'
    rocq_of_ocaml == reference
  end

  def rocq_cmd
    "rocq c -R tests Tests -R proofs RocqOfOCaml -impredicative-set #{generated_name}"
  end

  def rocq
    system("#{rocq_cmd} 2>/dev/null")
    return $?.exitstatus == 0
  end

  def extraction_cmd
    disable_fatal_warnings = "-lflags '-warn-error -a'"
    "cd tests/extraction && rocq c -R .. Tests -R ../../proofs RocqOfOCaml -impredicative-set extract.v && ocamlbuild #{disable_fatal_warnings} #{base_name}.byte && ./#{base_name}.byte"
  end

  def extraction
    FileUtils.rm_rf(["tests/extraction"])
    FileUtils.mkdir_p("tests/extraction")
    File.open("tests/extraction/extract.v", "w") do |f|
      f << <<-EOF
Require Import Tests.#{base_name}.

Recursive Extraction Library #{base_name}.
      EOF
    end
    system("(#{extraction_cmd}) >/dev/null")
    return $?.exitstatus == 0
  end
end

class ProjectResultModuleFieldTest < Test
  def initialize
    @directory = 'tests/project_result_module_field'
    super(File.join(@directory, 'Consumer.ml'))
  end

  def rocq_of_ocaml_cmd
    ['rocq-of-ocaml', '-project-cmt-dir', '<temporary CMT directory>', @source_file]
  end

  def capture_translation(command, directory)
    output, error, status = Open3.capture3(*command, chdir: directory)
    unless status.success?
      warn "Command failed: #{command.join(' ')}"
      warn error unless error.empty?
      return nil
    end
    output.force_encoding('utf-8').lines.drop(1).join
  end

  def check
    executable = File.expand_path('_build/default/src/rocqOfOCaml.exe')
    snapshots = {}
    Dir.mktmpdir('rocq-of-ocaml-project-test') do |directory|
      ['Provider.ml', 'Project.ml', 'Consumer.ml', 'Consumer.json'].each do |name|
        FileUtils.cp(File.join(@directory, name), directory)
      end
      compile_commands = [
        ['ocamlc', '-bin-annot', '-c', 'Provider.ml'],
        ['ocamlc', '-bin-annot', '-I', '.', '-c', 'Project.ml'],
        ['ocamlc', '-bin-annot', '-I', '.', '-c', 'Consumer.ml']
      ]
      return false unless compile_commands.all? do |command|
        system(*command, chdir: directory, out: File::NULL, err: File::NULL)
      end
      snapshots['Provider.v'] =
        capture_translation(
          [executable, '-output', '/dev/stdout', 'Provider.ml'],
          directory
        )
      snapshots['Consumer.v'] =
        capture_translation(
          [
            executable,
            '-config', 'Consumer.json',
            '-project-cmt-dir', '.',
            '-output', '/dev/stdout',
            'Consumer.ml'
          ],
          directory
        )
    end
    return false if snapshots.values.any?(&:nil?)
    if ENV['UPDATE_SNAPSHOTS'] == '1'
      snapshots.each do |name, contents|
        File.write(File.join(@directory, name), contents)
      end
    end
    snapshots.all? do |name, contents|
      contents == File.read(File.join(@directory, name), encoding: 'utf-8')
    end
  end

  def rocq_cmd
    "rocq c Provider.v, then Consumer.v, with #{@directory} mapped to TestProject"
  end

  def rocq
    common = [
      '-Q', 'proofs', 'RocqOfOCaml',
      '-Q', @directory, 'TestProject',
      '-impredicative-set'
    ]
    system('rocq', 'c', *common, File.join(@directory, 'Provider.v'),
      out: File::NULL, err: File::NULL) &&
      system('rocq', 'c', *common, File.join(@directory, 'Consumer.v'),
        out: File::NULL, err: File::NULL)
  end
end

class NegativeTest < Test
  def initialize(source_file, json_mode = false)
    super(source_file)
    @json_mode = json_mode
  end

  def error_file_name
    @source_file + '.errors'
  end

  def snapshot_name
    File.join(File.dirname(@source_file), base_name + '.errors')
  end

  def rocq_of_ocaml_cmd
    super(@json_mode ? ['-json-mode'] : [])
  end

  def normalize(output)
    output.force_encoding('utf-8').gsub(/\e\[[0-9;]*m/, '')
  end

  def rocq_of_ocaml_error
    FileUtils.rm_f(error_file_name)
    output, error, status = Open3.capture3(*rocq_of_ocaml_cmd)
    return nil if status.success?
    content =
      if @json_mode
        return nil unless File.exist?(error_file_name)
        File.read(error_file_name, :encoding => 'utf-8')
      else
        output + error
      end
    normalize(content)
  ensure
    FileUtils.rm_f(error_file_name)
  end

  def reference
    FileUtils.touch snapshot_name unless File.exist?(snapshot_name)
    File.read(snapshot_name, :encoding => 'utf-8')
  end

  def update
    File.write(snapshot_name, rocq_of_ocaml_error)
  end

  def check
    update if ENV['UPDATE_ERROR_SNAPSHOTS'] == '1'
    rocq_of_ocaml_error == reference
  end
end

class DefaultOutputTest < Test
  def generated_default_file
    without_extension = File.join(File.dirname(@source_file), base_name)
    extension = File.extname(@source_file)
    new_extension = extension == '.mli' ? '_mli.v' : '.v'
    File.join(File.dirname(without_extension), File.basename(without_extension).capitalize + new_extension)
  end

  def rocq_of_ocaml_cmd
    local_executable = '_build/default/src/rocqOfOCaml.exe'
    rocq_of_ocaml =
      ARGV[0] == '--with-coverage' ?
        ['dune', 'exec', '--instrument-with', 'bisect_ppx', 'src/rocqOfOCaml.exe', '--'] :
        [File.executable?(local_executable) ? local_executable : 'rocq-of-ocaml']
    [*rocq_of_ocaml, @source_file]
  end

  def check
    reference_contents =
      File.binread(generated_name) if File.exist?(generated_name)
    FileUtils.rm_f(generated_default_file)
    output, error, status = Open3.capture3(*rocq_of_ocaml_cmd)
    status.success? &&
      File.exist?(generated_default_file) &&
      (output + error).include?(generated_default_file)
  ensure
    FileUtils.rm_f(generated_default_file)
    File.binwrite(generated_name, reference_contents) if reference_contents
  end
end

class NoInputTest < Test
  def initialize
    super('no input')
  end

  def rocq_of_ocaml_cmd
    local_executable = '_build/default/src/rocqOfOCaml.exe'
    rocq_of_ocaml =
      ARGV[0] == '--with-coverage' ?
        ['dune', 'exec', '--instrument-with', 'bisect_ppx', 'src/rocqOfOCaml.exe', '--'] :
        [File.executable?(local_executable) ? local_executable : 'rocq-of-ocaml']
    rocq_of_ocaml
  end

  def check
    output, error, status = Open3.capture3(*rocq_of_ocaml_cmd)
    status.success? && (output + error).include?('Usage:')
  end
end

class AssumptionWarningTest < Test
  def check
    output, error, status = Open3.capture3(*rocq_of_ocaml_cmd)
    status.success? &&
      error.include?('assertion failure is represented by an Unreachable result') &&
      output.include?('RocqOfOCaml.Basics.Unreachable int') &&
      !output.match?(/forall.*Unreachable/)
  end
end

class Tests
  def initialize(source_files)
    @tests =
      source_files
        .sort_by {|source_file| source_file.respond_to?(:source_file) ? source_file.source_file : source_file }
        .map {|source_file| source_file.is_a?(Test) ? source_file : Test.new(source_file) }
    @valid_tests = 0
    @invalid_tests = 0
  end

  def print_result(result)
    if result
      @valid_tests += 1
      print " \e[1;32m✓\e[0m "
    else
      @invalid_tests += 1
      print " \e[31m✗\e[0m "
    end
  end

  def check
    puts "\e[1mChecking '.v':\e[0m"
    for test in @tests do
      print_result(test.check)
      puts test.rocq_of_ocaml_cmd.join(" ")
    end
  end

  def rocq
    puts "\e[1mRunning Rocq (compiles the reference files):\e[0m"
    for test in @tests do
      print_result(test.rocq)
      puts test.rocq_cmd
    end
  end

  def extraction
    puts "\e[1mCompiling and running the extracted programs:\e[0m"
    for test in @tests do
      if File.extname(test.source_file) != ".mli" then
        print_result(test.extraction)
        puts test.extraction_cmd
      end
    end
  end

  def print_summary
    puts
    puts "Total: #{@valid_tests} / #{@valid_tests + @invalid_tests}."
  end

  def invalid?
    @invalid_tests != 0
  end
end

test_files = Dir.glob('tests/*.ml*').select do |file_name|
  not file_name.include?("disabled")
end
tests = Tests.new(test_files + [ProjectResultModuleFieldTest.new])
tests.check
puts
tests.rocq

negative_tests = Tests.new([
  NegativeTest.new('tests/errors/legacy_attribute.ml'),
  NegativeTest.new('tests/errors/lazy_pattern.ml'),
  NegativeTest.new('tests/errors/unsupported_expressions.ml'),
  NegativeTest.new('tests/errors/unsupported_signature.mli'),
  NegativeTest.new('tests/errors/unknown_attribute_json.ml', true)
])
negative_tests.check

cli_tests = Tests.new([
  DefaultOutputTest.new('tests/top_level_definition.ml'),
  DefaultOutputTest.new('tests/functor.mli'),
  AssumptionWarningTest.new('tests/assert.ml'),
  NoInputTest.new
])
cli_tests.check

# We do not test the extraction for now as it fails due to axioms. We will see
# how to deal with it latter.
# tests.extraction
tests.print_summary
negative_tests.print_summary
cli_tests.print_summary

exit(1) if tests.invalid? || negative_tests.invalid? || cli_tests.invalid?
