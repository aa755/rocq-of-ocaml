require 'fileutils'
require 'json'
require 'open3'
require 'tmpdir'

root = File.expand_path('../..', __dir__)
executable = File.join(root, '_build/default/src/rocqOfOCaml.exe')
runtime = File.expand_path(ENV.fetch('ROCQ_RUNTIME', File.join(root, 'proofs')))
legacy_flags = ENV.key?('ROCQ_RUNTIME') ? [] : ['-impredicative-set']

Dir.mktmpdir('rocq-module-laws') do |dir|
  FileUtils.cp(Dir[File.join(__dir__, '*.{ml,json,v}')], dir)
  FileUtils.mkdir_p(File.join(dir, 'metadata'))
  run = lambda do |*command|
    output, error, status = Open3.capture3(*command, chdir: dir)
    abort "#{command.join(' ')}\n#{output}\n#{error}" unless status.success?
    output
  end
  compile = lambda do |name|
    run.call('rocq', 'c', '-Q', runtime, 'RocqOfOCaml', *legacy_flags, "#{name}.v")
  end
  %w[Provider Consumer Client].each do |name|
    run.call('ocamlc', '-bin-annot', '-I', '.', '-c', "#{name}.ml")
    command = [executable, '-project-cmt-dir', '.',
      '-assumption-metadata-dir', 'metadata',
      '-assumption-metadata-output', "metadata/#{name}.rocq-assumptions",
      '-assumption-prefix', name, '-output', "#{name}.v"]
    command.concat(['-config', "#{name}.json"]) if File.exist?(File.join(dir, "#{name}.json"))
    run.call(*command, "#{name}.ml")
    generated = File.read(File.join(dir, "#{name}.v"))
    abort "unsafe generated declaration in #{name}" if generated.match?(/\b(?:Axiom|Parameter|Admitted|Admit)\b|Unset Guard|bypass_check/)
    compile.call(name)
    compile.call('LawSupport') if name == 'Provider'
  end
  output = compile.call('Assertions')
  abort "unexpected proof assumptions:\n#{output}" if output.include?('Axioms:')
  reports = output.scan(/Closed under the global context|Set is impredicative/)
  abort 'missing assumption checks' unless reports.length == 5

  config = JSON.parse(File.read(File.join(dir, 'Consumer.json')))
  config['module_laws'][0][3] = ['Missing']
  File.write(File.join(dir, 'invalid.json'), JSON.generate(config))
  _, error, status = Open3.capture3(executable, '-project-cmt-dir', '.',
    '-config', 'invalid.json', '-output', '/dev/stdout', 'Consumer.ml', chdir: dir)
  abort 'unknown law parameter accepted' if status.success?
  abort 'wrong law parameter diagnostic' unless error.include?('unknown functor parameter Missing')
end

puts 'Module laws: local and cross-file propagation, concrete proof, and rejection checks passed.'
