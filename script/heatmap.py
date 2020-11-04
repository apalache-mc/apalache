#!/usr/bin/env python3
#
# Parse the profiling info that is produced with --smtprof and produce a heatmap.
# If this script is too slow, we should use the hierarchical structure of the code
# regions. For now, the code is using sorted lists instead.
#
# Igor Konnov, 2020

import csv
import html
import itertools
import re
import sys

class ProfileEntry:
    """Profiling data"""
    def __init__(self, weight, ncells, nconsts, nexprs):
        self.weight = weight
        self.ncells = ncells
        self.nconsts = nconsts
        self.nexprs = nexprs

    def add(self, other):
        self.weight += other.weight
        self.ncells += other.ncells
        self.nconsts += other.nconsts
        self.nexprs += other.nexprs

class CodeRegion:
    """An hierarchical code region that carries profiling data"""

    def __init__(self, filename, fromPos, toPos, profEntry):
        self.filename = filename
        self.fromPos = fromPos
        self.toPos = toPos
        self.profEntry = profEntry
        # sort by (end_line, start_line)
        self.sort_key = (toPos[0], fromPos[0])

    def rangeByLine(self, line_no, width):
        if self.fromPos[0] > line_no or self.toPos[0] < line_no:
            return (-1, -1)

        if self.fromPos[0] < line_no:
            if self.toPos[0] > line_no:
                # the region spans the whole line
                return (1, width)
            else:
                # the region starts on a preceding line but end on this one
                return (1, self.toPos[1])
        else:
            if self.toPos[0] > line_no:
                # the region starts on this line but ends later
                return (self.fromPos[1], width)
            else:
                # the region starts and ends on this line
                return (self.fromPos[1], self.toPos[1])

    def isInside(self, other):
        self.filename = other.filename \
                and self.fromPos >= outer.fromPos \
                and self.toPos <= outer.toPos


# the regular expression for the source location as produced by SANY
REGION_RE = re.compile(r"(.*):(\d+):(\d+)-(\d+):(\d+)")

def region_from_csv(row):
    m = REGION_RE.match(row[4])
    if m:
        entry = ProfileEntry(int(row[0]), int(row[1]), int(row[2]), int(row[3]))
        return CodeRegion(m.group(1),
                      (int(m.group(2)), int(m.group(3))), 
                      (int(m.group(4)), int(m.group(5))),
                      entry)
    else:
        print("Invalid source location: {}".format(row[4]), file=sys.stderr)
        return None


def merge_same_regions(sorted_regions):
    """The profiling data contains several points for the same range. Merge them."""
    prev_r = None
    new_regions = []
    for r in sorted_regions:
        if prev_r and prev_r.fromPos == r.fromPos and prev_r.toPos == r.toPos:
            # merge the data points
            prev_r.profEntry.add(r.profEntry)
        else:
            new_regions.append(r)

        prev_r = r

    return new_regions


def heat_color(weight, max_weight):
    h = int(110 * (1.0 - float(weight) / max_weight))
    return "hsl({}, 100%, 50%)".format(h)


def find_max_weight(regions):
    """Find the maximal weight in the given regions"""

    mw = 0
    for r in regions:
        mw = max(mw, r.profEntry.weight)

    return mw


def write_heatmap(heatfile, code_filename, regions):
    """Write code lines with while coloring them by code regions"""


    def drop_old_regions(regions, line_no):
        # remove the regions that end before line_no
        return list(itertools.dropwhile(lambda r: r.toPos[0] < line_no, regions))

    def split_line_by_regions(regions_ahead, line, line_no):
        line_len = len(line)
        # take the regions that cover the current line
        window = itertools.takewhile(lambda r: r.fromPos[0] <= line_no, regions_ahead)
        line_regions = sorted(list(window),
                # first, sort by the starting column; then by the nr. of lines
                key=lambda r: \
                        (r.rangeByLine(line_no, line_len)[0], r.toPos[0] - r.fromPos[0]))

        #print("Line: {}, length: {}".format(line_no, line_len))
        # Some regions span the whole line, as they come from compound expressions.
        # Partition the regions into more fine-grained pieces,
        # where the smaller regions have priority over the larger regions.
        point_set = set([1, line_len])
        for r in line_regions:
            (start, end) = r.rangeByLine(line_no, line_len)
            if start == -1 or end == -1:
                print("Broken region: {}:{}-{}:{}".\
                        format(r.fromPos[0], r.fromPos[1], r.toPos[0], r.toPos[1]), \
                        file=sys.stderr)
            point_set.add(start)
            point_set.add(end)

        #print("Ranges: {}".format([r.rangeByLine(line_no, line_len) for r in line_regions]))

        all_points = sorted(point_set)
        #print ("Points: {}".format(all_points))
        regions_to_partition = line_regions
        points_and_regions = []
        for p in all_points:
            # remove the regions before the point
            left_regions = \
                list(itertools.dropwhile(lambda r: r.rangeByLine(line_no, line_len)[1] < p,\
                                    regions_to_partition))
            # assign the first region in the list, it is the best one in the order
            if left_regions == []:
                # the last region ended before the last point
                if p != line_len and p != 1:
                    print("Point {} is neither 0, nor {}".format(p, line_len), \
                          file=sys.stderr)

                points_and_regions.append((p, None))
            else:
                best_cover = left_regions[0]
                (start, _) = best_cover.rangeByLine(line_no, line_len)
                if start <= p:
                    points_and_regions.append((p, best_cover))
                else:
                    # the point ends one region, while the next region starts later
                    points_and_regions.append((p, None))

        # split line into chunks, some of them annotated with regions
        chunks = []
        for ((start, r), (end, _)) in \
                zip(points_and_regions, points_and_regions[1:] + [(line_len, None)]):
            chunks.append((line[start - 1: end - 1], r))

        return chunks


    regions_ahead = merge_same_regions(sorted(regions, key=lambda r: r.sort_key))
    max_weight = find_max_weight(regions_ahead)

    with open(code_filename, 'r') as codefile:
        line_no = 1
        for line in codefile.readlines():
            print('<div style="clear: both;">', file=heatfile)
            print('<div class="code" style="float: left; width: 6em">{}:&nbsp;</div>'\
                    .format(line_no),
                    file=heatfile)
            regions_ahead = drop_old_regions(regions_ahead, line_no)
            chunks = split_line_by_regions(regions_ahead, line, line_no)

            for (text, region) in chunks:
                color = heat_color(region.profEntry.weight, max_weight) \
                        if region else "#ffffff"

                html_text = html.escape(text).replace(" ", "&nbsp;")
                print('<div class="code" style="float: left; background-color: {};">{}</div>' \
                        .format(color, html_text), file=heatfile)

            line_no += 1
            print('</div>', file=heatfile)


if __name__ == "__main__":
    args = sys.argv[1:]
    if len(args) < 2:
        print("Use: {} input.csv output.html".format(sys.argv[0]))
        sys.exit(1)

    csv_name, html_name = args[0:2]

    # parse the code regions and profiling statistics from CSV
    with open(csv_name, newline='') as csvfile:
        reader = csv.reader(csvfile, delimiter=',')
        headers = next(reader, None)
        regions_by_filename = {}
        for row in reader:
            r = region_from_csv(row)
            if r:
                if r.filename in regions_by_filename:
                    regions_by_filename[r.filename].append(r)
                else:
                    regions_by_filename[r.filename] = [r]

    # output simple html
    with open(html_name, 'w+') as heatfile:
        print("""
<html>
  <head>
    <style>
      .code {
        font-size: 12pt; font-family: "Courier New", Courier, monospace;
      }
    </style>
  </head>
  <body>
    <h2>What is that?</h2>

    <p>This is a heatmap of your TLA+ specification that was produced by
        <a href="https://github.com/informalsystems/apalache">Apalache</a>.
        We are using the following heat palette:
    </p>
        """, file=heatfile)

        print("""
        <p>We are using the following palette: <div style="float:left"><b>cold</b>&nbsp;</div>
        """, file=heatfile)

        for w in range(0, 41):
            text = '<div style="float: left; background-color: {}; border: 1px; width: 1em;">&nbsp;</div>'\
                    .format(heat_color(w, 40))
            print(text, file=heatfile)

        print("""&nbsp;<b>hot</b></p>""", file=heatfile)

        print("""
    <p>This heatmap shows the relative complexity of translating the specification
       in SMT (by Apalache). An expression that is closer to the hot end of the spectrum
       produces the larger portion of SMT constraints and constants. It does not
       always mean that the respective SMT problem is harder, but usually it is
       a symptom of blowing up in the number of constraints. It also shows which
       expressions are not efficiently translated by the current version of Apalache.
    </p>
    <p>
       Currently, we measure the weights individually in every TLA+ module.
       As a result, a hot expression in one module may produce significantly
       fewer expressions than a hot expression in another module.
    </p>
  """, file=heatfile)

        for filename in regions_by_filename.keys():
            print("<h2>Module {}</h2>".format(html.escape(filename)), file=heatfile)
            write_heatmap(heatfile, filename, regions_by_filename[filename])

        print("</body><html>", file=heatfile)

