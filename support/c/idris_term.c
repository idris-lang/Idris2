#ifdef _WIN32

#include <windows.h>

int idris2_getTermCols() {
    CONSOLE_SCREEN_BUFFER_INFO csbi;
    GetConsoleScreenBufferInfo(GetStdHandle(STD_OUTPUT_HANDLE), &csbi);
    return (int) csbi.srWindow.Right - csbi.srWindow.Left + 1;
}

int idris2_getTermLines() {
    CONSOLE_SCREEN_BUFFER_INFO csbi;
    GetConsoleScreenBufferInfo(GetStdHandle(STD_OUTPUT_HANDLE), &csbi);
    return (int) csbi.srWindow.Bottom - csbi.srWindow.Top + 1;
}

#else

#include <sys/ioctl.h>

int idris2_getTermCols() {
    struct winsize ts;
    ioctl(0, TIOCGWINSZ, &ts);
    return (int) ts.ws_col;
}

int idris2_getTermLines() {
    struct winsize ts;
    ioctl(0, TIOCGWINSZ, &ts);
    return (int) ts.ws_row;
}

#endif
