const support_system_signal_process = require('process')

const support_system_signal_sighup = 'SIGHUP'
const support_system_signal_sigint = 'SIGINT'
const support_system_signal_sigabrt = 'SIGABRT'
const support_system_signal_sigquit = 'SIGQUIT'
const support_system_signal_sigill = 'SIGILL'
const support_system_signal_sigsegv = 'SIGSEGV'
const support_system_signal_sigtrap = 'SIGTRAP'
const support_system_signal_sigfpe = 'SIGFPE'
const support_system_signal_sigusr1 = 'SIGUSR1'
const support_system_signal_sigusr2 = 'SIGUSR2'

function support_system_signal_ignoreSignal(signal) {
    support_system_signal_process.on(signal, sig => {})
    return 0
}

function support_system_signal_sendSignal(pid, signal) {
    support_system_signal_process.kill(pid, signal)
    return 0
}

function support_system_signal_raiseSignal(signal) {
    support_system_signal_process.kill(support_system_signal_process.pid, signal)
    return 0
}

function support_system_signal_defaultSignal(signal) {
    // TODO
}

function support_system_signal_collectSignal(signal) {
    // TODO
}

function support_system_signal_handleNextCollectedSignal() {
    // TODO
}
