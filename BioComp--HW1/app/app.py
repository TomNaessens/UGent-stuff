import SuffixTree.SubstringDict
import os
import sys


def wordsplitter(word):
    yield (1, 1, word)

    for stepsize in range(2, len(word)-1):
        for startindex in range(0, stepsize):
            yield (startindex, stepsize, word[startindex:len(word):stepsize])


i = int(sys.argv[1])
chunkSize = int(sys.argv[2])

fastalines = open('data/cleaned.fa').readlines()[i*chunkSize:(i+1)*chunkSize]
proteins = [tuple(line.split()) for line in fastalines]

dictionary = open('data/famous.txt').readlines()
dictionary = [line.strip() for line in dictionary]

for header, protein in proteins:
    d = SuffixTree.SubstringDict()

    for start, step, word in wordsplitter(protein):
        d[word] = (header, word, start, step)

    for word in dictionary:
        for wor, reversed in [(word, False), (word[::-1], True)]:
            found = d[wor]
            if found:
                for prot, found, start, step in found:
                    startindex = found.find(wor)*step+start

                    if reversed:
                        startindex += (len(wor)-1)*step
                        step = step*-1

                    print "{} {} {} {}".format(header, word, startindex, step)

# For some reason (probably because C bindings), the garbage collector
# keeps running and running so we'll force-kill this.
os._exit(0)
