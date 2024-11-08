import fs from "node:fs";

export function prim__changeDir(d) {
  try {
    process.chdir(d)
    return 0
  } catch (e) {
    process.__lasterr = e
    return 1
  }
}

export function prim__createDir(d) {
  try {
    fs.mkdirSync(d)
    return 0
  } catch (e) {
    process.__lasterr = e
    return 1
  }
}

export function prim__openDir(d) {
  try {
    return fs.opendirSync(d)
  } catch (e) {
    process.__lasterr = e
    return null
  }
}

export function prim__closeDir(d) {
  try {
    d.closeSync()
  } catch (e) {
    process.__lasterr = e
    return null
  }
}

export function prim__removeDir(d) {
  try {
    fs.rmdirSync(d)
    return 0
  } catch (e) {
    process.__lasterr = e
    return 1
  }
}

export function prim__dirEntry(d) {
  try {
    const dir = d.readSync()
    if (dir == null) {
      return null
    } else {
      return dir.name
    }
  } catch (e) {
    process.__lasterr = e
    return null
  }
}
