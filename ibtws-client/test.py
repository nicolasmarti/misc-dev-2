import Pyro.EventService.Clients
import string
import random

from time import *
import pygtk
pygtk.require('2.0')
import gtk
from types import *
from threading import *

from datetime import *

gtk.gdk.threads_init()


from pytz import timezone
import pytz

from Pyro.EventService.Clients import Subscriber

class ClockWindow(gtk.Window):

    def __init__(self):
        gtk.Window.__init__(self, gtk.WINDOW_TOPLEVEL)
        self.connect("delete_event", delete)
        self.set_border_width(10)

        self.zone = [("NewYork", timezone('US/Eastern')),
                     ("London", timezone('Europe/London')),
                     ("Singapore/HK", timezone('Asia/Singapore')),
                     ("Tokyo", timezone('Asia/Tokyo'))
                     ]
        
    def loop(self):
        while True:
            gtk.gdk.threads_enter()
            title = ""
            for i in self.zone:
                cnow = datetime.now(i[1])
                title += cnow.strftime(i[0] + " %d/%m/%Y %H:%M:%S       ")
            self.set_title(title)
            gtk.gdk.threads_leave()
            sleep(0.5)


class InfoFrame(gtk.Frame, Subscriber):
    
    def __init__(self, name, types, names, key, event):

        gtk.Frame.__init__(self)
        Subscriber.__init__(self)

        self.setThreading(0)
        
        self.set_label(name)

        self.key = key

        self.set_border_width(10)
        self.set_size_request(1000, 600)
        self.show()        

        # build a table to put all my stuffs
        self.table = gtk.Table(100, 100, True)
        self.table.show()
        self.add(self.table)

        # build scrolled window and textview
        self.sw = gtk.ScrolledWindow()
        self.sw.set_policy(gtk.POLICY_AUTOMATIC, gtk.POLICY_AUTOMATIC)

        colsty = []
        for i in types:
            colsty.append(str)

        self.liststore = gtk.ListStore(*colsty)
        self.listview = gtk.TreeView(self.liststore)

        for i in range(0, len(names)):
            cell = gtk.CellRendererText()
            column = gtk.TreeViewColumn(names[i])
            self.listview.append_column(column)
            column.pack_start(cell, True)
            column.add_attribute(cell, 'markup', i)

        self.listview.show()
        self.sw.add(self.listview)
        self.sw.show()
        self.table.attach(self.sw, 0, 100, 0, 100)

        self.key2iter = dict()
        
        self.subscribe(event)        

        self.types = types

    def loop(self):
        print "enter loop"
        self.listen()
        print "exit loop"
        return False

    def event(self, event):
        if not event.msg[self.key] in self.key2iter:
            gtk.gdk.threads_enter()
            a = [ '<span background="white"><b>' + str(x) + '</b></span>' for x in event.msg]
            self.key2iter[event.msg[self.key]] = [self.liststore.append(a), event.msg]
            gtk.gdk.threads_leave()
        else:
            for i in range(0, len(event.msg)):
                gtk.gdk.threads_enter()
                if self.types[i] == int or self.types[i] == float:
                    old = self.key2iter[event.msg[self.key]][1][i]
                    if old > event.msg[i]:
                        color = "red"
                    elif old < event.msg[i]:
                        color = "green"
                    else:
                        color = "grey"
                        
                else:
                    color = "white"

                txt = '<span background="' + color + '"><b>' + str(event.msg[i]) + '</b></span>'
                self.liststore.set(self.key2iter[event.msg[self.key]][0], i, txt)
                gtk.gdk.threads_leave()

            self.key2iter[event.msg[self.key]][1] = event.msg

                

class StockPublisher(Pyro.EventService.Clients.Publisher):
    def __init__(self, channel):
        Pyro.EventService.Clients.Publisher.__init__(self)
        self.channel = channel

        self.seq = ["GS",
                    "GOOG",
                    "8604",
                    "STAN",
                    "MSFT",
                    "AAPL",
                    "DOUDOU",
                    "DIDI"]

    def publishQuote(self, data):
        self.publish(self.channel, data)

    def loop(self):
        while True:
            ticker = random.choice(self.seq)            
            self.publishQuote((ticker, int(random.random()*100), random.random()*1000, random.random()*1000, int(random.random()*100)))
            sleep(0.1)



def main():

    gtk.gdk.threads_enter()
    gtk.main()
    gtk.gdk.threads_leave()

    return 0

def delete(widget, event=None):
    gtk.main_quit()
    return False

if __name__ == "__main__":
    window = ClockWindow()
    th = Thread(target=window.loop)
    th.daemon = True
    th.start()
    
    notebook = gtk.Notebook()
    notebook.set_tab_pos(gtk.POS_TOP)
    notebook.show()
    window.add(notebook)
    
    frame1=InfoFrame("Stock Quote", [str, int, float, float, int], ["ticker", "bid size", "bid quote", "ask quote", "ask size"], 0, "StockQuotes")
    th = Thread(target=frame1.loop)
    th.daemon = True
    th.start()
    notebook.append_page(frame1, gtk.Label(frame1.get_label()))

    frame2=InfoFrame("Stock Quote", [str, int, float, float, int], ["ticker", "bid size", "bid quote", "ask quote", "ask size"], 0, "StockQuotes2")
    th = Thread(target=frame2.loop)
    th.daemon = True
    th.start()
    notebook.append_page(frame2, gtk.Label(frame2.get_label()))


    sp1 = StockPublisher("StockQuotes")
    th = Thread(target=sp1.loop)
    th.daemon = True
    th.start()

    sp2 = StockPublisher("StockQuotes")
    th = Thread(target=sp2.loop)
    th.daemon = True
    th.start()
    


    window.show_all()

    main()
