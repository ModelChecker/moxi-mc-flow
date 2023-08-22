from subprocess import Popen, PIPE, TimeoutExpired
from pathlib import Path

from datetime import datetime

test_file_paths = ["nuxmv-examples/vis/QF_BV/"]

# test_file_paths = ["nusmv-examples/", # -- works
                #    "nuxmv-examples/beem/QF_BV/", # -- works
                #    "nuxmv-examples/growing-counters/",  # -- TODO: LTLSPEC
                #    "nuxmv-examples/hybrid-automata/QF_LRA/", # -- UNSUPPORTED: reals
                #    "nuxmv-examples/invgen/QF_BV/", -- works
                #    "nuxmv-examples/invgen/QF_LIA/", -- works
                #    "nuxmv-examples/ltlsat-polimi/", -- TODO: LTLSPEC
                #    "nuxmv-examples/lustre/QF_LIA/", -- TODO: max recursion depth bc of parens
                #    "nuxmv-examples/software/QF_BV/",
                #    "nuxmv-examples/software/QF_LRA/", -- UNSUPPORTED: reals
                #    "nuxmv-examples/svcomp/QF_BV/",
                #    "nuxmv-examples/svcomp/QF_LRA/", -- UNSUPPORTED: reals
                #    "nuxmv-examples/systemc/QF_BV/",
                #    "nuxmv-examples/systemc/QF_LRA/", -- UNSUPPORTED: reals
                #    "nuxmv-examples/threads/QF_LIA/",
                #    "nuxmv-examples/vcegar/arrays/",  -- TODO: string concat?
                #    "nuxmv-examples/vcegar/QF_BV/",  -- TODO: string concat?
                #    "nuxmv-examples/vis/arrays/",  -- TODO: array operations (CONSTARRAY)
                #    "nuxmv-examples/vis/QF_BV/"]  -- TODO: complex idents issues? - shouldn't parse according to spec?

failure_list = ["guidance.smv"]

def main():
    curr_time = datetime.now().strftime('%Y-%m-%d %H:%M:%S')
    timeout = 10

    print("TEST RUN at " + curr_time + " (test case timeout = " + str(timeout) + ")")

    dir = Path("./examples")

    trials, successes, failures, timeouts, skipping = [], [], [], [], []

    global test_file_paths
    for test_file_path in test_file_paths:
        file_list = [f.name for f in dir.glob(test_file_path + "*.smv") if f.is_file]

        lfile_list = len(file_list)
        curr_file_no = 0
        for filename in file_list:
            curr_file_no += 1
            prefix = "(" + str(curr_file_no) + "/" + str(lfile_list) + ") "
            trials.append(filename)
            global failure_list
            if filename in failure_list:
                skipping.append(filename)
                print(prefix + filename, "in failure list: SKIPPING!")
                continue
            cmd = "python3 src/nuxmv-prototype/nuxmv_pyparser.py " + "examples/" + test_file_path + filename
            process = Popen(cmd, shell=True, stdout=PIPE, stderr=PIPE)
            try:
                stdout, stderr = process.communicate(timeout=timeout)
                success = (stderr == b'')
                if success:
                    successes.append(filename)
                    print(prefix + filename + ": SUCCESS!")
                else:
                    failures.append(filename)
                    print(prefix + filename + ": FAILURE!")
            except TimeoutExpired:
                timeouts.append(filename)
                process.kill()
                print(prefix + filename + ": TIMED OUT!")

        print("PARSER RESULTS FOR FILES IN " + test_file_path)
        print("===============================================")
        ltrials = len(trials)
        print("SUCCESS:", len(successes), "/", ltrials)
        print("FAILURE:", len(failures), "/", ltrials)
        print("TIMEOUTS:", len(timeouts), "/", ltrials)
        print("SKIPPING:", len(skipping), "/", ltrials)
        
        if len(skipping) == 0:
            continue
        else:
            print("-- SKIPPED")
            for s in skipping:
                print("----", s)
        
        if len(failures) == 0:
            print("NO CORRECTNESS ERRORS!")
        else:
            print("PARSE ERRORS ON")
            for f in failures:
                print(f)

    # nusmv_file_list = [f.name for f in dir.glob("nusmv-examples/") if f.is_file]
    # nuxmv_beem_QF_BV_file_list = [f.name for f in dir.glob("nuxmv-examples/beem/QF_BV/") if f.is_file]


    # for filename in nuxmv_beem_QF_BV_file_list: # nusmv_file_list:
    #     if filename in failure_list:
    #         continue
    #     cmd = "python3 src/nuxmv-prototype/nuxmv_pyparser.py " + "examples/nuxmv-examples/beem/QF_BV/" + filename
    #     process = Popen(cmd, shell=True, stdout=PIPE, stderr=PIPE)
    #     try:
    #         stdout, stderr = process.communicate(timeout=10)
    #         success = (stderr == b'')
    #         if success:
    #             print(filename + " - SUCCESS")
    #         else:
    #             print("FAILURE on file " + filename + " - exiting")
    #             break
    #     except TimeoutExpired:
    #         process.kill()
    #         print(filename + " - TIMEOUT")




if __name__ == '__main__':
    main()