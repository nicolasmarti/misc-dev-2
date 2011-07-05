try:
  from xml.etree import ElementTree
except ImportError:
  from elementtree import ElementTree
import time
import getpass
import gdata.spreadsheet.service
import gdata.service
import atom.service
import gdata.spreadsheet
import gdata.spreadsheet.text_db
import atom
import getopt
import sys
import string
from time import *

def PrintFeed(feed):
  for i, entry in enumerate(feed.entry):
    if isinstance(feed, gdata.spreadsheet.SpreadsheetsCellsFeed):
      print '%s %s\n' % (entry.title.text, entry.content.text)
    elif isinstance(feed, gdata.spreadsheet.SpreadsheetsListFeed):
      print '%s %s %s' % (i, entry.title.text, entry.content.text)
      # Print this row's value for each column (the custom dictionary is
      # built from the gsx: elements in the entry.) See the description of
      # gsx elements in the protocol guide.
      print 'Contents:'
      for key in entry.custom:
        print '  %s: %s' % (key, entry.custom[key].text)
      print '\n',
    else:
      print '%s %s\n' % (i, entry.title.text)

class GoogleSheet():

    def __init__(self, username, passwd):
        
        # connection
        self.gd_client = gdata.spreadsheet.service.SpreadsheetsService()
        self.gd_client.email = username
        self.gd_client.password = passwd
        self.gd_client.source = 'GoogleSheet'
        self.gd_client.ProgrammaticLogin()
        self.curr_key = ''
        self.curr_wksht_id = ''
        self.list_feed = None

    def getSheetNames(self):
        
        self.sheets = dict()

        feed = self.gd_client.GetSpreadsheetsFeed()
        for i, entry in enumerate(feed.entry):
            sheet_name = entry.title.text
            id_parts = feed.entry[i].id.text.split('/')
            sheet_key = id_parts[len(id_parts) - 1]
            self.sheets[sheet_name] = dict()
            self.sheets[sheet_name]["key"] = sheet_key
            self.sheets[sheet_name]["workingsheet"] = dict()

            #print str(i) + " := " + sheet_name + "(" + sheet_key + ")"
            ws = self.gd_client.GetWorksheetsFeed(sheet_key)

            for i, entry in enumerate(ws.entry):
                worksheet_name = entry.title.text
                id_parts = ws.entry[i].id.text.split('/')
                worksheet_key = id_parts[len(id_parts) - 1]
                self.sheets[sheet_name]["workingsheet"][worksheet_name] = worksheet_key
                #print "\t" + str(i) + " := " + worksheet_name + "(" + worksheet_key + ")"            
    
        return None

    def getData(self, sheet_name, worksheetname, cell):
        try:
            curr_key = self.sheets[sheet_name]["key"]
            curr_wksht_id = self.sheets[sheet_name]["workingsheet"][worksheetname]
            list_feed = self.gd_client.GetCellsFeed(curr_key, curr_wksht_id)
            for i, entry in enumerate(list_feed.entry):
              if isinstance(cell, str) and entry.title.text == cell:
                print entry.content
                return (entry.content.text, entry.cell.inputValue)
              else:
                if str(cell[0]) == entry.cell.col and str(cell[1]) == entry.cell.row:
                  print entry.content
                  return (entry.content.text, entry.cell.inputValue)

        except Exception as e: 
            print e
            return None

    def getCells(self, sheet_name, worksheetname):
        try:
            res = []
            curr_key = self.sheets[sheet_name]["key"]
            curr_wksht_id = self.sheets[sheet_name]["workingsheet"][worksheetname]
            list_feed = self.gd_client.GetCellsFeed(curr_key, curr_wksht_id)
            for i, entry in enumerate(list_feed.entry):
                res.append((entry.title.text, (int(entry.cell.col), int(entry.cell.row)), (entry.content.text, entry.cell.inputValue)))

            return res

        except Exception as e: 
            print e
            return None

    def setData(self, sheet_name, worksheetname, col, row, value):
        try:

            key = self.sheets[sheet_name]["key"]
            wksht_id = self.sheets[sheet_name]["workingsheet"][worksheetname]
            entry = self.gd_client.UpdateCell(row=row, col=col, inputValue=value, key=key, wksht_id=wksht_id)
            if isinstance(entry, gdata.spreadsheet.SpreadsheetsCell):
                return value
            
            return None

        except Exception as e: 
            print e
            return None
            

#WARNING: to reset before pushing !!!        
username = ''
password = ''


if __name__ == '__main__':
  if not username:
    username = raw_input('Please enter your username: ')
  if not password:
    password = getpass.getpass()  
  
  gs = GoogleSheet(username, password)
  gs.getSheetNames()
  #print gs.sheets
  #print gs.getCells("cppi","Feuille5")
  #print gs.getData("cppi","Feuille5", "B6")
  #print gs.getData("cppi","Feuille5", (2, 6))
  #print gs.setData("cppi","Feuille5", 2, 6, "5%")
  print gs.getData("progsheet", "Sheet1", "G4")
  print gs.setData("progsheet", "Sheet1", 7, 4, "=1+8")
