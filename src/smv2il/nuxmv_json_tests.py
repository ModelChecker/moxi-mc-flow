"""
This file runs all specified tests through the nuxmv-json pipeline
"""
from subprocess import PIPE, Popen, TimeoutExpired

test_file_paths = [
    # ALL OF THESE WORK
    "examples/smv/nusmv-examples/counter.smv",
    "examples/smv/nusmv-examples/short.smv",
    "examples/smv/nuxmv-examples/lustre/QF_LIA/_6counter.smv",
    "examples/smv/nuxmv-examples/lustre/QF_LIA/_6counter2.smv",
    "examples/smv/nuxmv-examples/lustre/QF_LIA/_6countern.smv",
    "examples/smv/nuxmv-examples/lustre/QF_LIA/_6counters_e3_140_e8_149.smv",
    "examples/smv/nuxmv-examples/lustre/QF_LIA/_6counters_e8_371_e1_448.smv",
    "examples/smv/nuxmv-examples/lustre/QF_LIA/_6counters_e8_371_e1_448.smv",
    "examples/smv/nuxmv-examples/lustre/QF_LIA/_6counters_e8_371_e2_80.smv",
    "examples/smv/nuxmv-examples/lustre/QF_LIA/_6counters_e8_371_e3_224.smv",
    "examples/smv/nuxmv-examples/lustre/QF_LIA/_6counters_e8_371_e7_304.smv",
    "examples/smv/nuxmv-examples/lustre/QF_LIA/_6counters.smv",
    "examples/smv/nuxmv-examples/lustre/QF_LIA/car_1_e7_184_e3_299.smv",
    "examples/smv/nuxmv-examples/lustre/QF_LIA/car_1.smv",
    "examples/smv/nuxmv-examples/lustre/QF_LIA/car_2_e7_1027_e1_1047.smv",
    "examples/smv/nuxmv-examples/lustre/QF_LIA/car_2_e7_1027_e7_359.smv",
    "examples/smv/nuxmv-examples/lustre/QF_LIA/car_2_e8_491_e7_826.smv",
    "examples/smv/nuxmv-examples/lustre/QF_LIA/car_2.smv",
    "examples/smv/nuxmv-examples/lustre/QF_LIA/car_3_e1_586.smv",
    "examples/smv/nuxmv-examples/lustre/QF_LIA/car_3_e1_924.smv"
]

def main():
    trials, successes, failures, timeouts, skipping = [], [], [], [], []

    timeout = 10
    curr_file_no = 0
    global test_file_paths
    lfile_list = len(test_file_paths)
    prefix = "(" + str(curr_file_no) + "/" + str(lfile_list) + ") " 

    for test_file_path in test_file_paths:
        curr_file_no += 1
        json_file_path_full = test_file_path.split(".")[0]
        test_name = test_file_path.split("/")[-1]
        test = test_name.split(".")[0]
        json_file_path_stub = test + ".json"
        json_file_path = '/'.join(__file__.split("/")[:-1]) + "/" + json_file_path_stub


        # print(f"test_file_path = {test_file_path}, json_file_path = {json_file_path}")

        cmd = "python3 src/smv2il/nuxmv_json.py " + test_file_path + " " + json_file_path
        process = Popen(cmd, shell=True, stdout=PIPE, stderr=PIPE)
        try:
            stdout, stderr = process.communicate(timeout=timeout)
            if stdout.find(b'PASSED') == -1:
                print(test, "- TEST FAILED!")
                print("Here's the failing test's command: ", cmd)
                break
            else:
                print(test, "- TEST PASSED!")
        except TimeoutExpired:
            timeouts.append(test)
            process.kill()

if __name__ == "__main__":
    main()