import child_process from 'child_process';

export function prim__system(cmd) {
  const options = { shell: true, stdio: 'inherit' }
  const { status } = child_process.spawnSync(cmd, [], options)
  return status
}

// call with overwrite == 0 to avoid overwriting an existing variable.
export function prim__setEnv(name, value, overwrite) {
  if (overwrite == 0 && process.env[name]) {
    return 0
  }
  process.env[name] = value
  return 0
}

export function prim__unsetEnv(name) {
  delete process.env[name]
  return 0
}
