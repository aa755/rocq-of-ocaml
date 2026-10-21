require 'fileutils'
require 'open3'
require 'tmpdir'

root = File.expand_path('../..', __dir__)
executable = File.join(root, '_build/default/src/rocqOfOCaml.exe')
runtime = File.expand_path(ENV.fetch('ROCQ_RUNTIME', File.join(root, 'proofs')))
legacy_flags = ENV.key?('ROCQ_RUNTIME') ? [] : ['-impredicative-set']

Dir.mktmpdir('rocq-ppx-stdlib-aliases') do |dir|
  FileUtils.cp(File.join(__dir__, 'Input.ml'), dir)
  run = lambda do |*command|
    output, error, status = Open3.capture3({'DUNE_ROOT' => dir}, *command, chdir: dir)
    abort "#{command.join(' ')}\n#{output}\n#{error}" unless status.success?
    output
  end
  File.write(File.join(dir, 'dune-project'), "(lang dune 3.8)\n")
  File.write(File.join(dir, 'dune'),
    "(library (name fixture) (modules Input) (libraries ppx_deriving.runtime))\n")
  run.call('dune', 'build', '--root', dir, 'fixture.cma')
  run.call(executable, '-project-cmt-dir', '_build/default/.fixture.objs/byte',
    '-output', 'Input.v', 'Input.ml')
  generated = File.read(File.join(dir, 'Input.v'))
  abort 'unresolved PPX set or map alias' if
    generated.match?(/Ppx_deriving_runtime\.(?:_Set|Map)/)
  %w[OCamlSet.S.add OCamlSet.S.mem OCamlMap.S.add OCamlMap.S.find_opt].each do |name|
    abort "missing executable operation #{name}" unless generated.include?(name)
  end
  run.call('rocq', 'c', '-Q', runtime, 'RocqOfOCaml', *legacy_flags, 'Input.v')
end

puts 'PPX standard-library aliases: set and map operations compile.'
