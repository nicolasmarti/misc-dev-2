from Mymms import *
import types
import sys
import os
from curses import *
from time import sleep

mymmsrequire("base")
mymmsrequire("fundamental")


stdscr = initscr()
start_color()
noecho()
cbreak()
stdscr.keypad(1)


#begin_x = 20 ; begin_y = 7
#height = 5 ; width = 40
#win = newwin(height, width, begin_y, begin_x)
stdscr.refresh()

#stdscr.addstr(0, 0, "Current mode: Typing mode", A_REVERSE)
#stdscr.refresh()

#stdscr.addstr( "Pretty text", color_pair(1) )
#stdscr.refresh()

#init_pair(1, COLOR_RED, COLOR_WHITE)
#stdscr.addstr(20,10, "RED ALERT!", color_pair(1) )

x = 0
y = 0

(maxy, maxx) = stdscr.getmaxyx()

stdscr.hline(maxy/2,0,'-',maxx)

stdscr.vline(maxy/2+1,maxx/2,'|',maxy)

while 1:
    c = stdscr.getch()
    if c == ord('q'): break  # Exit the while()
    elif c == KEY_HOME: x = y = 0
    elif c == ord('p'): 
        stdscr.addstr(y, x, "p")
        if x + 1>= maxx:
            x=0
            y = y+1
        else:
            x = x+1
            


nocbreak(); stdscr.keypad(0); echo()
endwin()

