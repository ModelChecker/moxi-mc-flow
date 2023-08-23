"""
This file runs all specified tests through the nuxmv-json pipeline
"""
from subprocess import PIPE, Popen, TimeoutExpired

test_file_paths = [
    "high-level/examples/nusmv-examples/counter.smv",
    "high-level/examples/nusmv-examples/short.smv",
    "high-level/examples/nuxmv-examples/lustre/QF_LIA/_6counter.smv",
    "high-level/examples/nuxmv-examples/lustre/QF_LIA/_6counter2.smv"
    # "high-level/examples/nuxmv-examples/lustre/QF_LIA/_6countern.smv"
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

        cmd = "python3 high-level/src/nuxmv-prototype/nuxmv-json.py " + test_file_path + " " + json_file_path
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