#!/usr/bin/env python
"""
usage: orgtest.py program_path testfile_path
"""
# test runner based on learntris
from __future__ import print_function # let's keep it 3.x compatible
import sys, os, glob, subprocess, difflib, pprint, time, re
import extract

class TestFailure(Exception):
    def __init__(self, msg):
        self.msg = msg

    def __str__(self):
        return self.msg

class TimeoutFailure(TestFailure):
    pass

commentPattern = re.compile(r"(?<!\\)#.*")
def parse_test(lines):
    """
    :: [Str] -> [(Op, Str)] , where Op in { 'in', 'out' }
    """
    for line in lines:
        # strip comments, but leave \# intact.
        line = commentPattern.sub("", line)
        line = line.replace(r"\#", "#")
        sline = line.strip()
        if sline == "":                # skip empty lines
            pass
        elif sline[0] == '>':          # input to send
            yield ('in', sline[1:].strip())
        else:                          # expected output
            yield ('out', sline)

def spawn(program_name):
    return subprocess.Popen([program_name],
                            stdin=subprocess.PIPE,
                            stdout=subprocess.PIPE)


def await_results(program, timeout_seconds=2):
    """
    This polls the child program until it finishes
    executing. If it takes more than =timeout_seconds=,
    kill the program and raise a TimeoutFailure.
    """
    countdown = timeout_seconds * 10
    while program.poll() is None and countdown > 0:
        time.sleep(0.1) # seep for 1/10 of a second
        countdown -= 1
    if countdown == 0:
        program.kill()
        raise TimeoutFailure("<program timed out>")
    else: pass


def run_test(program, opcodes):
    # separate the test script into input and output lines:
    given    = [op[1] for op in opcodes if op[0] == 'in']
    expected = [op[1] for op in opcodes if op[0] == 'out']

    # send all the input lines:
    print("---- sending commands ----")
    for cmd in given:
        print(cmd)
        program.stdin.write(cmd + "\n")
    program.stdin.close()
    # let the program do its thing:
    print("---- expected results ----")
    for line in expected:
        print(line)

    print("---- awaiting results ----")
    await_results(program)

    # read all the actual output lines, and compare to expected:
    actual = [line for line in program.stdout.read().split("\n") if line]

    if actual != expected:
        diff = list(difflib.Differ().compare(actual, expected))
        raise TestFailure('output mismatch:\n%s'
                          % pprint.pformat(diff))

def run_tests(program_path, testfile_path):
    for i, test in enumerate(extract.tests(testfile_path)):
        program = spawn(program_path)
        opcodes = list(parse_test(test.lines))
        print("Running test %d: %s" % (i+1, test.name))
        try:
            run_test(program, opcodes)
            print("Test %d passed" % (i+1))
        except (TimeoutFailure, TestFailure) as e:
            print("Test %d failed: %s" % (i+1, e))
            break
        print("\n") # add 2 blank lines between tests


def check_path(path):
    if os.path.exists(path):
        return True
    else:
        print("Error: ('%s') not found." % path)
        return False


def main():
    try:
        _, program, testfile = sys.argv
    except:
        print(__doc__)
    else:
        if check_path(program) and check_path(testfile):
            run_tests(program, testfile)

if __name__ == '__main__':
    main()
