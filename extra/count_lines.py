import csv
import sys

def parse_input(input_lines):
    parsed_lines = []
    for line in input_lines:
        stripped = line.strip()
        print("stripped: " + str(stripped))
        print("\n")
        if "comments" not in stripped:
            spec, proof, comments, filename = stripped.split()
            print ("Filename: " + str(filename))
            print ("Spec: " + str(spec))
            print ("Proof: " + str(proof))
            print ("Comments: " + str(proof))
            parsed_lines.append([filename, spec, proof, comments])
    return parsed_lines

def main():
    input_lines = sys.stdin.readlines()
    parsed_lines = parse_input(input_lines)

    # Writing to CSV
    with open('count_lines.csv', 'w', newline='') as csvfile:
        writer = csv.writer(csvfile)
        writer.writerow(['filename', 'spec', 'proof', 'comments'])  # Writing header
        writer.writerows(parsed_lines)

if __name__ == "__main__":
    main()
