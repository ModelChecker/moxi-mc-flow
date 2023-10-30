"""
This file runs all specified tests through the nuxmv-json pipeline
"""
from subprocess import PIPE, Popen, TimeoutExpired
import sys
import os.path
import glob

test_file_paths = [
    # ALL OF THESE WORK
    "examples/smv/nusmv-examples/counter.smv",
    "examples/smv/nusmv-examples/short.smv",
    # "examples/smv/nuxmv-examples/lustre/QF_LIA/_6counter.smv",
    # "examples/smv/nuxmv-examples/lustre/QF_LIA/_6counter2.smv",
    # "examples/smv/nuxmv-examples/lustre/QF_LIA/_6countern.smv",
    # "examples/smv/nuxmv-examples/lustre/QF_LIA/_6counters_e3_140_e8_149.smv",
    # "examples/smv/nuxmv-examples/lustre/QF_LIA/_6counters_e8_371_e1_448.smv",
    # "examples/smv/nuxmv-examples/lustre/QF_LIA/_6counters_e8_371_e1_448.smv",
    # "examples/smv/nuxmv-examples/lustre/QF_LIA/_6counters_e8_371_e2_80.smv",
    # "examples/smv/nuxmv-examples/lustre/QF_LIA/_6counters_e8_371_e3_224.smv",
    # "examples/smv/nuxmv-examples/lustre/QF_LIA/_6counters_e8_371_e7_304.smv",
    # "examples/smv/nuxmv-examples/lustre/QF_LIA/_6counters.smv",
    # "examples/smv/nuxmv-examples/lustre/QF_LIA/car_1_e7_184_e3_299.smv",
    # "examples/smv/nuxmv-examples/lustre/QF_LIA/car_1.smv",
    # "examples/smv/nuxmv-examples/lustre/QF_LIA/car_2_e7_1027_e1_1047.smv",
    # "examples/smv/nuxmv-examples/lustre/QF_LIA/car_2_e7_1027_e7_359.smv",
    # "examples/smv/nuxmv-examples/lustre/QF_LIA/car_2_e8_491_e7_826.smv",
    # "examples/smv/nuxmv-examples/lustre/QF_LIA/car_2.smv",
    # "examples/smv/nuxmv-examples/lustre/QF_LIA/car_3_e1_586.smv",
    # "examples/smv/nuxmv-examples/lustre/QF_LIA/car_3_e1_924.smv",
    # "examples/smv/nuxmv-examples/lustre/QF_LIA/car_3_e2_695.smv",
    # "examples/smv/nuxmv-examples/lustre/QF_LIA/car_3_e2_777.smv",
    # "examples/smv/nuxmv-examples/lustre/QF_LIA/car_3_e7_626_e1_305.smv",
    # "examples/smv/nuxmv-examples/lustre/QF_LIA/car_3_e7_626.smv",
    # "examples/smv/nuxmv-examples/lustre/QF_LIA/car_3_e8_33_e1_856.smv",
    # "examples/smv/nuxmv-examples/lustre/QF_LIA/car_3_e8_33_e2_1010.smv",
    # "examples/smv/nuxmv-examples/lustre/QF_LIA/car_3_e8_33_e7_220.smv",
    # "examples/smv/nuxmv-examples/lustre/QF_LIA/car_3_e8_33.smv",
    # "examples/smv/nuxmv-examples/lustre/QF_LIA/car_3.smv",
    # "examples/smv/nuxmv-examples/lustre/QF_LIA/car_4_e3_57_e4_1047.smv",
    "examples/smv/nuxmv-examples/beem/QF_BV/adding.1.prop1-back-serstep.btor.smv",
    # "examples/smv/nuxmv-examples/beem/QF_BV/adding.1.prop1-func-interl.btor.smv",
    # "examples/smv/nuxmv-examples/invgen/QF_BV/apache-escape-absolute.c.smv"

    # TIMEOUT
    # "examples/smv/nuxmv-examples/ltlsat-polimi/krca1p1.smv"
]
# beem_benchmarks = glob.glob("examples/smv/nuxmv-examples/beem/QF_BV/*.smv")
# test_file_paths += beem_benchmarks

longest_basename_size = max([len(os.path.basename(tfp.split("/")[-1])) for tfp in test_file_paths])
print(longest_basename_size)
script_str = "python3 {} {}"
test_format_str = "{:<" + str(longest_basename_size) + "} {:<25}"

CRED    = '\33[31m'
CGREEN  = '\33[32m'
CEND    = '\033[0m'


def main():
    print(test_format_str.format("[test name]", "[status]"))
    trials, successes, failures, timeouts, skipping = [], [], [], [], []

    timeout = 10
    curr_file_no = 0
    global test_file_paths
    lfile_list = len(test_file_paths)
    prefix = "(" + str(curr_file_no) + "/" + str(lfile_list) + ") " 

    for test_file_path in test_file_paths:
        (base, ext) = os.path.splitext(test_file_path)
        pp_file_path = base + "-pp" + ext
        json_file_path = base + ".json"

        test_name = base.split("/")[-1]

        preprocess_cmd = script_str.format("src/smv2mcil/preprocess.py", test_file_path)
        test_cmd = script_str.format("src/smv2mcil/nuxmv_json.py", pp_file_path) + " " + json_file_path
        
        process = Popen(preprocess_cmd, shell=True, stdout=PIPE, stderr=PIPE)
        process.communicate(timeout=timeout)

        process = Popen(test_cmd, shell=True, stdout=PIPE, stderr=PIPE)
        try:
            stdout, stderr = process.communicate(timeout=timeout)
            if stdout.find(b'PASSED') == -1:
                ret = test_format_str.format(test_name, f"{CRED} TEST FAILED! {CEND}")
                print(ret)
                print("Here's the failing test's command: ", test_cmd)
                break
            else:
                ret = test_format_str.format(test_name, f"{CGREEN} TEST PASSED! {CEND}")
                print(ret)
        except TimeoutExpired:
            timeouts.append(test_name)
            process.kill()

if __name__ == "__main__":
    main()