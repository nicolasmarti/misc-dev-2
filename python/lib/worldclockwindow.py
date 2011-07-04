import pygtk
pygtk.require('2.0')
import gobject 
import gtk

from time import *
from threading import *
from datetime import *
from pytz import timezone
import pytz

class WorldClockWindow(gtk.Window, Thread):

    def __init__(self, glock):
        gtk.Window.__init__(self)
        Thread.__init__(self)
        
        self.glock = glock
        self.connect("delete_event", self.delete)
        self.set_border_width(10)

        self.daemon = True
        self.set_size_request(800, 400)

    def run(self):
        l = [(timezone('US/Eastern'), "NY"), 
             (timezone('Europe/London'), "London"), 
             (timezone('Europe/Paris'), "Paris"), 
             (timezone('Asia/Singapore'), "HK"), 
             (timezone('Asia/Tokyo'), "Tokyo")]
        while True:
            mstr = ""
            for d in l:
                mnow = datetime.now(d[0])
                mstr += d[1] + mnow.strftime(" %d/%m/%Y %H:%M:%S   ")
            self.glock.acquire()
            gtk.gdk.threads_enter()
            #print "enter time"
            self.set_title(mstr)
            #print "exit time"
            gtk.gdk.threads_leave()
            self.glock.release()
            sleep(1)
        return False

    def delete(self, widget, event=None):
        gtk.main_quit()
        return False

