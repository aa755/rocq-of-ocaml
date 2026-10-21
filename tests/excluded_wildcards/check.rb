require 'fileutils'
require 'json'
require 'open3'
require 'tmpdir'

root = File.expand_path('../..', __dir__)
translator = File.join(root, '_build/default/src/rocqOfOCaml.exe')

Dir.mktmpdir('excluded-wildcards-') do |directory|
  %w[mapper.ml input.ml].each do |file|
    FileUtils.cp(File.join(__dir__, file), directory)
  end
  File.write(File.join(directory, 'dune-project'), "(lang dune 3.19)\n")
  File.write(File.join(directory, 'dune'), <<~DUNE)
    (executable
      (name mapper)
      (modules mapper)
      (libraries compiler-libs.common))
    (library
      (name fixture)
      (modules input)
      (flags (:standard -w -a -ppx #{File.join(directory, '_build/default/mapper.exe').inspect})))
  DUNE
  commands = [
    ['dune', 'build', '--root', directory, 'mapper.exe'],
    ['dune', 'build', '--root', directory, 'fixture.cma']
  ]
  commands.each do |command|
    output, errors, status = Open3.capture3(*command, chdir: directory)
    raise "#{command.join(' ')}\n#{output}\n#{errors}" unless status.success?
  end
  File.write(File.join(directory, 'config.json'), JSON.generate(
    excluded_definitions: [['*', 'to_yojson'], ['*', 'Nested.to_yojson']]
  ))
  output, errors, status = Open3.capture3({'DUNE_ROOT' => directory}, translator,
    '-config', 'config.json', '-output', 'Input.v', 'input.ml',
    chdir: directory)
  raise "translation failed\n#{output}\n#{errors}" unless status.success?
  generated = File.read(File.join(directory, 'Input.v'))
  raise 'excluded alias survived' if generated.include?('to_yojson')
  raise "retained alias was dropped\n#{generated}\n#{errors}" unless generated.include?(':= kept.')
  raise 'application was dropped' unless generated.include?('kept 2')
  runtime = ENV.fetch('EXCLUDED_WILDCARDS_RUNTIME', File.join(root, 'proofs'))
  flags = ENV['EXCLUDED_WILDCARDS_RUNTIME'] ? [] : ['-impredicative-set']
  output, errors, status = Open3.capture3('rocq', 'c',
    '-Q', runtime, 'RocqOfOCaml', *flags, 'Input.v', chdir: directory)
  raise "generated file failed Rocq\n#{output}\n#{errors}" unless status.success?
end

puts 'Excluded wildcard aliases: generated aliases pruned, applications retained.'
