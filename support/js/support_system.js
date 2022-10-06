const support_system_child_process = require('child_process')

function support_system_spawnSync(cmd) {
  const options = { shell: true, stdio: 'inherit' }
  const { status } = support_system_child_process.spawnSync(cmd, [], options)
  return status
}

// call with overwrite == 0 to avoid overwriting an existing variable.
function support_system_setEnv(name, value, overwrite) {
  if (overwrite == 0 && process.env[name]) {
    return 0
  }
  process.env[name] = value
  return 0
}

function support_system_unsetEnv(name) {
  delete process.env[name]
  return 0
}

