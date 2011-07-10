# This program is free software: you can redistribute it and/or modify
# it under the terms of the GNU General Public License as published by
# the Free Software Foundation, either version 3 of the License, or
# (at your option) any later version.
#
# This program is distributed in the hope that it will be useful,
# but WITHOUT ANY WARRANTY; without even the implied warranty of
# MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
# GNU General Public License for more details.
#
# You should have received a copy of the GNU General Public License
# along with this program.  If not, see <http://www.gnu.org/licenses/>.
#
import urllib2
import re
from types import *
from datetime import *

# A simple HTML table parser. It turns tables (including nested tables) into arrays
# Nigel Sim <nigel.sim@gmail.com>
# http://simbot.wordpress.com
# http://projects.nigelsim.org
from HTMLParser import HTMLParser
import re, string, os
from string import lower

class Table(list):
    pass
class Row(list):
    pass
class Cell(list):
    """The cell holds components of text and HTML anchors"""
    def append(self,item):
        s = super(Cell, self)
        if isinstance(item, str):
            if len(self) == 0 or isinstance(top(self), str):
                if len(self) > 0:
                    i = len(self)-1
                    self[i] = self[i] + item
                else:
                    s.append(item)
            elif isinstance(top(self), Anchor):
                s.append(item)
        else:
            s.append(item)
class Anchor(object):
    """HTML Anchor"""
    def __init__(self, href):
        self.href = href
        self.text = None
    def append(self, text):
        self.text = text
    def __str__(self):
        return '<a href="%s">%s</a>'%(self.href, self.text)
    def __repr__(self):
        """Possible not the best repr"""
        return '{"href": "%s", "text": "%s"}'%(self.href, self.text)
class Image(object):
    def __init__(self, src):
        self.src = src
    def __repr__(self):
        return '{"src": "%s"}'%(self.src)
# Get the item on the top of a stack
def top(x):
    return x[len(x)-1]
class TableParser(HTMLParser):
    def __init__(self, parser=None, anchors=True):
        """
        The parser is a method which will be passed the doc at the end
        of the parsing. Useful if TableParser is within an inner loop and
        you want to automatically process the document. If it is omitted then
        it will do nothing
        """
        self._tag = None
        self._buf = None
        self._attrs = None
        self.doc = None # Where the document will be stored
        self._stack = None
        self._parser = parser
        self.reset()
        self.anchors = anchors
        return
    def reset(self):
        HTMLParser.reset(self)
        self.doc = []
        self._stack = [self.doc]
        self._buf = ''
    def close(self):
        HTMLParser.close(self)
        if self._parser != None:
            self._parser(self.doc)
    def handle_starttag(self, tag, attrs):
        self._tag = tag
        self._attrs = attrs
        attrs = dict(attrs)
        if lower(tag) == 'table':
            self._buf = ''
            self._stack.append(Table())
        elif lower(tag) == 'tr':
            self._buf = ''
            self._stack.append(Row())
        elif lower(tag) == 'td':
            self._buf = ''
            self._stack.append(Cell())
        elif lower(tag) == 'a' and self.anchors and isinstance(top(self._stack), Cell):
            # add the text we already have
            if len(self._buf) > 0:
                top(self._stack).append(self._buf)
            self._buf = ''
            self._stack.append(Anchor(attrs['href']))
        elif lower(tag) == 'img' and self.anchors and isinstance(top(self._stack), Cell):
            # add the text we already have
            if len(self._buf) > 0:
                top(self._stack).append(self._buf)
            self._buf = ''
            top(self._stack).append(Image(attrs['src']))
        #print "Encountered the beginning of a %s tag" % tag
    def handle_endtag(self, tag):
        if lower(tag) == 'table':
            t = None
            while not isinstance(t, Table):
                t = self._stack.pop()
            r = top(self._stack)
            r.append(t)
        elif lower(tag) == 'tr':
            t = None
            while not isinstance(t, Row):
                t = self._stack.pop()
            r = top(self._stack)
            r.append(t)
        elif lower(tag) == 'td':
            c = None
            while not isinstance(c, Cell):
                c = self._stack.pop()
            t = top(self._stack)
            if isinstance(t, Row):
                if len(self._buf) > 0:
                    c.append(self._buf)
                t.append(c)
            else:
                print "Cell not in a row, rather in a %s"%t
        elif lower(tag) == 'a' and self.anchors and isinstance(top(self._stack), Anchor):
            a = None
            while not isinstance(a, Anchor):
                a = self._stack.pop()
            c = top(self._stack)
            if isinstance(c, Cell):
                a.append(self._buf)
                self._buf = ''
                c.append(a)
            else:
                print "anchor should be in a cell"
        self._tag = None
        #print "Encountered the end of a %s tag" % tag
    def handle_data(self, data):
        self._buf += data

# yahoo japan financial information crawler

def parseint(s):
    try:
        return int(s)
    except:
        findnum = re.findall("(\d)+?", s)
        n = ""
        for j in findnum:
            n += j
        return int(n)

def parsefloat(s):
    try:
        return float(s)
    except:
        findnum = re.findall("(\d|\.)+?", s)
        n = ""
        for j in findnum:
            n += j
        return float(n)
    

def parse_quote_table(data, res = None):
    if res == None:
        res = []
    for i in data:
        d = dict()
        finddates = re.findall("\d+", i[0][0], re.UNICODE)
        begindate = date(int(finddates[0]), int(finddates[1]), int(finddates[2]))
        d["date"] = begindate
        d["open"] = parsefloat(i[1][0])
        d["high"] = parsefloat(i[2][0])
        d["low"] = parsefloat(i[3][0])
        d["close"] = parsefloat(i[4][0])
        d["volume"] = parseint(i[5][0])
        d["ajust. close"] = parsefloat(i[6][0])
        res.append(d)

    return res


def parse_yahoo_quote_page(link):
    page = urllib2.urlopen(link).read()
    tables = re.findall('<table.*?</table>',page,re.S)
    p = TableParser()
    #print tables[1]
    p.feed(tables[1])
    return parse_quote_table(p.doc[0][1:])

#link = "http://stocks.finance.yahoo.co.jp/stocks/history/?code=8604.T"
#res = parse_yahoo_quote_page(link)
#for i in res:
#    print i

def buildlink(ticker, startdate, enddate, startrow):
    res = "http://table.yahoo.co.jp/t?"
    res += "c=" + str(startdate.year)
    res += "&a=" + str(startdate.month)
    res += "&b=" + str(startdate.day)
    res += "&f=" + str(enddate.year)
    res += "&d=" + str(enddate.month)
    res += "&e=" + str(enddate.day)
    res += "&g=d&s=" + ticker + ".t"
    res += "&y=" + str(startrow)
    res += "&z=" + ticker + ".t"
    res += "&x=sb"
    return res
    
def get_quote_table(link):
    page = urllib2.urlopen(link).read()
    tables = re.findall('<table.*?</table>',page,re.S)
    tables = re.findall('<table.*?</table>',tables[4][3:],re.S)
    p = TableParser()
    p.feed(tables[0])
    return p.doc[0][1:]

def get_historical(ticker, startdate, enddate = date.today()):
    
    res = []
    
    i = 0

    while True:
        try:
            link = buildlink(ticker, startdate, enddate, i*50)
            quotes = get_quote_table(link)
            parse_quote_table(quotes, res)
            i += 1
        except Exception as e:
            #print e
            return res

    return res

if __name__ == '__main__':
    for i in get_historical("8604", date(2008, 1, 1)):
        print i

