import argparse
import os
import sys
import csv

dir = os.path.realpath( os.path.dirname(__file__) )

print(dir)

parser = argparse.ArgumentParser(description="Runs Apalache tests.")
parser.add_argument("file", type=str, help="CSV file")
parser.add_argument("folder", type=str, help="Results Folder.")

args = parser.parse_args()

if not os.path.exists(args.file): 
  print(f"Error: File {args.file} does not exist.")
  sys.exit(1)

def ifArg( flag, val ):
  return "" if (val == "") else f"{flag}={val}"

pairs = map( lambda x: (f"--{x}",x), ["init", "inv", "length", "next", "search"])

with open( args.file, "r" ) as csvFile:
  reader = csv.DictReader(csvFile, delimiter=";")
  for row in reader:
    fileArgs = map( lambda x: ifArg(x[0],row[x[1]]), pairs )
    cmd = f"{dir}/runTest.sh {args.folder} {row['filename']} {' '.join(fileArgs)} {row['options']}"
    print(cmd)
    os.system( cmd )    
