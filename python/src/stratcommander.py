

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

username = ''
password = ''

from strat1 import Strat1
from strat2 import Strat2

def loop(username, passwd):

    # connection
    gd_client = gdata.spreadsheet.service.SpreadsheetsService()
    gd_client.email = username
    gd_client.password = passwd
    gd_client.source = 'StratCommander'
    gd_client.ProgrammaticLogin()
    curr_key = ''
    curr_wksht_id = ''
    list_feed = None

    # grab the spreadsheet
    feed = gd_client.GetSpreadsheetsFeed()
    for i, entry in enumerate(feed.entry):
        if entry.title.text == "StratCommander":
            index = i
    id_parts = feed.entry[index].id.text.split('/')
    curr_key = id_parts[len(id_parts) - 1]

    # grab the worksheet
    feed = gd_client.GetWorksheetsFeed(curr_key)

    for i, entry in enumerate(feed.entry):
      if entry.title.text == "Rimocon":
        index = i
    id_parts = feed.entry[index].id.text.split('/')
    curr_wksht_id = id_parts[len(id_parts) - 1]

    for i, entry in enumerate(feed.entry):
      if entry.title.text == "charts":
        index = i
    id_parts = feed.entry[index].id.text.split('/')
    curr_wksht_id2 = id_parts[len(id_parts) - 1]


    strats = []

    # loop of results
    
    while True:

      try:
        # read the configuration
        # update the strat
        list_feed = gd_client.GetListFeed(curr_key, curr_wksht_id)
      
        for i, entry in enumerate(list_feed.entry):

          # create/lookup the current strat dictionnary
          if i >= len(strats):
            strat = dict()
            strats.append(strat)
            print "new strat in slot: " + str(i)
          else:
            strat = strats[i]

          # put the values inside
          for key in entry.custom:  
            strat[key] = entry.custom[key].text

        # manage the strategies
        for j, i in enumerate(strats):

          #print "slot " + str(j) + ": " + str(i)
          
          # create the strat if not yet created, and activated
          if i["stratname"] == "strat1" and (not "strat" in i) and i["activated"] == "Y":
            #print "starting strat"
            # eval parameters
            print "params: " + i["params"]
            params = eval(i["params"])
            # create the strat
            strat = Strat1(params)
            # input it into the dict
            i["strat"] = strat
            i["strat"].daemon = True
            i["strat"].start()
            #print "activate slot: " + str(j)

          # create the strat if not yet created, and activated
          if i["stratname"] == "strat2" and (not "strat" in i) and i["activated"] == "Y":
            #print "starting strat"
            # eval parameters
            print "params: " + i["params"]
            params = eval(i["params"])
            # create the strat
            strat = Strat2(params)
            # input it into the dict
            i["strat"] = strat
            i["strat"].daemon = True
            i["strat"].start()
            #print "activate slot: " + str(j)

          # if deactivated, and a strat is already running: stop it
          if "strat" in i and i["activated"] <> "Y" and i["strat"].opened == True:
            #print "deactivating strat"
            i["strat"].close()
            #print "deactivate slot: " + str(j)

          # if activated, and a strat is stopped: run it
          if "strat" in i and i["activated"] == "Y" and i["strat"].opened == False:
            #print "reactivating strat"
            i["strat"].open()
            #print "reactivate slot: " + str(j)

      except Exception as inst:
        print "stratcommander error: " + str(inst)
        pass

      # show the results
      for i, entry in enumerate(strats):
        try:
          print "entry = " + str(entry)

          state = entry["strat"].state
          position = entry["strat"].c["position"]
          upnl = entry["strat"].c["upnl"]
          rpnl = entry["strat"].c["rpnl"]
          pnl = upnl + rpnl

          gd_client.UpdateCell(row=i+2, 
                               col=4, 
                               inputValue=str(state), 
                               key=curr_key, wksht_id=curr_wksht_id)


          gd_client.UpdateCell(row=i+2, 
                               col=5, 
                               inputValue=str(position), 
                               key=curr_key, wksht_id=curr_wksht_id)

          gd_client.UpdateCell(row=i+2, 
                               col=6, 
                               inputValue=str(upnl), 
                               key=curr_key, wksht_id=curr_wksht_id)
          
          gd_client.UpdateCell(row=i+2, 
                               col=7, 
                               inputValue=str(rpnl), 
                               key=curr_key, wksht_id=curr_wksht_id)
          
          gd_client.UpdateCell(row=i+2, 
                               col=8, 
                               inputValue=str(pnl), 
                               key=curr_key, wksht_id=curr_wksht_id)

          #gd_client.UpdateCell(row=i+2, 
          #                       col=9, 
          #                       inputValue=str(((entry["strat"].pose - entry["strat"].originpose)/entry["strat"].originpose) * 100.0) + "%", 
          #                       key=curr_key, wksht_id=curr_wksht_id)

          gd_client.UpdateCell(row=i+2, 
                                 col=1, 
                                 inputValue=entry["strat"].c.toGoogleChart(), 
                                 key=curr_key, wksht_id=curr_wksht_id2)

          
          print "strat " + str(i) + ": state = " + str(state) + ", position = " + str(position) + ", upnl = " + str(upnl) + ", rpnl = " + str(rpnl) + ", pnl = " + str(pnl)

        # we should look for further strat / modif of the other
        except Exception as inst:
          print "output loop: " + str(inst)
          pass

    return None



if __name__ == '__main__':
  if not username:
    username = raw_input('Please enter your username: ')
  if not password:
    password = getpass.getpass()  
  loop(username, password)
