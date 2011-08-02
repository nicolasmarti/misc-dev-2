# for Mysql
import MySQLdb

# initialize cid
conn = MySQLdb.connect(host='localhost', db='finance', user='finance', passwd='lekiller')
curs = conn.cursor()

res = curs.execute('truncate ibcontract')
print res
curs.execute('select * from ibcontract')
result = curs.fetchall()
print len(result)

res = curs.execute('truncate iborder')
print res
curs.execute('select * from iborder')
result = curs.fetchall()
print len(result)

res = curs.execute('truncate orderexec')
print res
curs.execute('select * from orderexec')
result = curs.fetchall()
print len(result)

res = curs.execute('truncate ibquotesize')
print res
curs.execute('select * from ibquotesize')
result = curs.fetchall()
print len(result)

res = curs.execute('truncate ibquoteprice')
print res
curs.execute('select * from ibquoteprice')
result = curs.fetchall()
print len(result)
