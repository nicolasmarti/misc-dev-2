import MySQLdb
import types

conn = MySQLdb.connect(host='localhost', db='finance', user='finance', passwd='lekiller')
curs=conn.cursor()
curs.execute('select * from iborder where cid = 0 order by date')
result = curs.fetchall()

print result
#print type(result[0])
#print (type(result[0][0]), type(result[0][1]), type(result[0][2]), type(result[0][3]))

sum = 0
vol = 0
for i in result:
    sum += i[3] * i[2]
    vol += i[2]
print sum
print vol
conn.close()
