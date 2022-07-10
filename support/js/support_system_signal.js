const support_system_signal_process = require('process')

// https://en.wikipedia.org/wiki/Signal_(IPC)#Default_action
const support_system_signal_sighup = 1
const support_system_signal_sigint = 2
const support_system_signal_sigquit = 3
const support_system_signal_sigill = 4
const support_system_signal_sigtrap = 5
const support_system_signal_sigabrt = 6
const support_system_signal_sigfpe = 8
const support_system_signal_sigusr1 = 10
const support_system_signal_sigsegv = 11
const support_system_signal_sigusr2 = 12

function signal_int_to_string(signal) {
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

function support_system_signal_ignoreSignal(signal) {
    let signal_string = signal_int_to_string(signal)
    try {
        support_system_signal_process.on(signal_string, sig => {})
        return 0
    } catch (e) {
        return -1
    }
}

function support_system_signal_sendSignal(pid, signal) {
    let signal_string = signal_int_to_string(signal)
    try {
        support_system_signal_process.kill(pid, signal_string)
        return 0
    } catch (e) {
        return -1
    }
}

function support_system_signal_raiseSignal(signal) {
    let signal_string = signal_int_to_string(signal)
    try {
        support_system_signal_process.kill(support_system_signal_process.pid, signal_string)
        return 0
    } catch (e) {
        return -1
    }
}

function support_system_signal_defaultSignal(signal) {
    let signal_string = signal_int_to_string(signal)
    try {
        support_system_signal_process.removeAllListeners(signal_string)
        return 0
    } catch (e) {
        return -1
    }
}

// this implementation deduplicates signals and leaves handle ordering up to details of the Map impl
var pending_signals = new Map();

function support_system_signal_collectSignal(signal) {
    let signal_string = system_signal_int_to_string(signal)
    try {
        support_system_signal_process.on(signal_string, x => { pending_signals.set(signal) })
        return 0
    } catch (e) {
        return -1
    }
}

function support_system_signal_handleNextCollectedSignal() {
    let next = pending_signals.keys().next()
    if (next.done) {
        return -1
    } else {
        let val = next.value
        pending_signals.delete(val)
        return val
    }
}
