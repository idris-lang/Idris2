import process from 'node:process';

// https://en.wikipedia.org/wiki/Signal_(IPC)#Default_action
export const prim__sighup = 1
export const prim__sigint = 2
export const prim__sigquit = 3
export const prim__sigill = 4
export const prim__sigtrap = 5
export const prim__sigabrt = 6
export const prim__sigfpe = 8
export const prim__sigusr1 = 10
export const prim__sigsegv = 11
export const prim__sigusr2 = 12

function _signal_int_to_string(signal) {
    switch (signal) {
        case 1:
            return 'SIGHUP'
        case 2:
            return 'SIGINT'
        case 3:
            return 'SIGQUIT'
        case 4:
            return 'SIGILL'
        case 5:
            return 'SIGTRAP'
        case 6:
            return 'SIGABRT'
        case 8:
            return 'SIGFPE'
        case 10:
            return 'SIGUSR1'
        case 11:
            return 'SIGSEGV'
        case 12:
            return 'SIGUSR2'
        default:
            // https://nodejs.org/api/process.html#signal-events
            // 0 can be sent to test for the existence of a process, it has no effect if the process exists, but will throw an error if the process does not exist.
            return 0
    }
}

export function prim__ignoreSignal(signal) {
    let signal_string = _signal_int_to_string(signal)
    try {
        process.on(signal_string, _sig => { })
        return 0
    } catch (_e) {
        return -1
    }
}

export function prim__defaultSignal(signal) {
    let signal_string = _signal_int_to_string(signal)
    try {
        process.removeAllListeners(signal_string)
        return 0
    } catch (_e) {
        return -1
    }
}

// this implementation deduplicates signals and leaves handle ordering up to details of the Map impl
const pending_signals = new Map();

export function signal_collectSignal(signal) {
    let signal_string = _signal_int_to_string(signal)
    try {
        process.on(signal_string, _x => { pending_signals.set(signal) })
        return 0
    } catch (_e) {
        return -1
    }
}

export function signal_handleNextCollectedSignal() {
    let next = pending_signals.keys().next()
    if (next.done) {
        return -1
    } else {
        let val = next.value
        pending_signals.delete(val)
        return val
    }
}

export function signal_sendSignal(pid, signal) {
    let signal_string = _signal_int_to_string(signal)
    try {
        process.kill(pid, signal_string)
        return 0
    } catch (_e) {
        return -1
    }
}

export function signal_raiseSignal(signal) {
    let signal_string = _signal_int_to_string(signal)
    try {
        process.kill(process.pid, signal_string)
        return 0
    } catch (_e) {
        return -1
    }
}
