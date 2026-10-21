require 'json'
require 'open3'
require 'tmpdir'

executable = '_build/default/src/rocqOfOCaml.exe'
output, warning, status = Open3.capture3(executable, '-output', '/dev/stdout',
  '-config', 'tests/checked_domain_recursion.json',
  'tests/checked_domain_recursion.ml')
abort 'checked-domain translation failed' unless status.success?
abort 'missing domain warning' unless warning.include?('explicit checked-domain boundary')
abort 'domain certificate introduced an assumption' if output.match?(/Admit|Axiom|Parameter/)

Dir.mktmpdir('checked-domain') do |dir|
  config = JSON.parse(File.read('tests/checked_domain_recursion.json'))
  config['termination_certificates'][0][-2] = ''
  path = File.join(dir, 'empty-domain.json')
  File.write(path, JSON.generate(config))
  _, error, status = Open3.capture3(executable, '-output', '/dev/stdout',
    '-config', path, 'tests/checked_domain_recursion.ml')
  abort 'accepted an empty domain' if status.success?
  abort 'wrong empty-domain diagnostic' unless error.include?('boolean domain')

  config = JSON.parse(File.read('tests/certified_well_founded_recursion.json'))
  config['termination_certificates'][1].concat(['true', '0'])
  path = File.join(dir, 'mutual-domain.json')
  File.write(path, JSON.generate(config))
  _, error, status = Open3.capture3(executable, '-output', '/dev/stdout',
    '-config', path, 'tests/certified_well_founded_recursion.ml')
  abort 'silently ignored a mutual domain' if status.success?
  abort 'wrong mutual-domain diagnostic' unless error.include?('single recursive definition')
end

puts 'Checked domains: explicit warning and unsupported cases checked.'
