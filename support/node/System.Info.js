import os from 'node:os'

export const prim__getNProcessors = () => os.cpus().length

// but implemented as %external, not %foreign
export function prim__os() {
  const o = os.platform()
  return o === 'linux' ? 'unix' : o === 'win32' ? 'windows' : o
}
