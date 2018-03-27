import sys
import os

libs = ""
for root, dirs, files in os.walk(sys.argv[1]):
    for file in files:
        if file.endswith(".jar"):
             libs=libs+":"+os.path.join(root, file)
print libs