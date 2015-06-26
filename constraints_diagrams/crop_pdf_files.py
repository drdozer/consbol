author = "Chris"

import argparse
import os
import sys
import subprocess

def process_arguments(args):
    parser = argparse.ArgumentParser(description="Convert from pdf to svg using inkscape")
    parser.add_argument('-d', dest="directory", type=str, help="Directory containing pdf files to convert", required=True)
    options = parser.parse_args(args)
    return vars(options)

opdict = process_arguments(sys.argv[1:])

directory = opdict["directory"]
ab_path = os.path.abspath(directory)
print ab_path

for i in os.listdir(ab_path):
    if i.endswith(".pdf"):
        file_name = os.path.splitext(i)[0]
        subprocess.call(["pdfcrop", ab_path + "/" + i, ab_path + '/' + i])