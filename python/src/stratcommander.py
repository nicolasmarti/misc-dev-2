

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
        if entry.title.text == "StratCommander":
            index = i
    id_parts = feed.entry[index].id.text.split('/')
    curr_wksht_id = id_parts[len(id_parts) - 1]

    # read the configuration
    strats = []

    list_feed = gd_client.GetListFeed(curr_key, curr_wksht_id)

    for i, entry in enumerate(list_feed.entry):
        strat = dict()
        strats.append(strat)
        for key in entry.custom:  
            strat[key] = entry.custom[key].text

    # start the strategies
    for i in strats:
        if i["stratname"] == "strat1":
            params = eval(i["options"])
            strat = Strat1(params)

        i["strat"] = strat
        i["strat"].start()

    print strats

    # loop of results
    sleep(10)
    while True:
        for i, entry in enumerate(strats):

            gd_client.UpdateCell(row=i+2, 
                                 col=3, 
                                 inputValue=str(entry["strat"].state), 
                                 key=curr_key, wksht_id=curr_wksht_id)

            gd_client.UpdateCell(row=i+2, 
                                 col=4, 
                                 inputValue=str(entry["strat"].c["position"]), 
                                 key=curr_key, wksht_id=curr_wksht_id)

            gd_client.UpdateCell(row=i+2, 
                                 col=5, 
                                 inputValue=str(entry["strat"].c["upnl"]), 
                                 key=curr_key, wksht_id=curr_wksht_id)

            gd_client.UpdateCell(row=i+2, 
                                 col=6, 
                                 inputValue=str(entry["strat"].c["pnl"]), 
                                 key=curr_key, wksht_id=curr_wksht_id)

            gd_client.UpdateCell(row=i+2, 
                                 col=7, 
                                 inputValue=str(((entry["strat"].pose - entry["strat"].originpose)/entry["strat"].originpose) * 100.0) + "%", 
                                 key=curr_key, wksht_id=curr_wksht_id)

    return None



if __name__ == '__main__':
  if not username:
    username = raw_input('Spreadsheets API | Text DB Tests\n'
                         'Please enter your username: ')
  if not password:
    password = getpass.getpass()  
  loop(username, password)
