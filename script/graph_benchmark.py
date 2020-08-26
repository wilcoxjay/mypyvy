import os
import sys
import re
import matplotlib.pyplot as plt
from ast import literal_eval

KOD_RESULTS_DIRECTORY_PATH = '/scr/amohamdy/mypyvy/benchmark_files/_KOD_RESULTS/'
Z3_RESULTS_DIRECTORY_PATH = '/scr/amohamdy/mypyvy/benchmark_files/_Z3_RESULTS/'
'''
{
    'lockserv':
    {
        ('request_msg', 1, 0):
        {
            (unsat, 3ms), (unsat, 5ms), (sat, 2ms)
        }
    }
}
'''
def get_filename(file, prefix, suffix):
    filename = os.path.basename(file)
    return filename[len(prefix):filename.find(suffix)]

def fill_params_map(files_map, run_files):
    for file in run_files:
        with open(file, 'r') as f:
            inpt = f.read()
            run_params = tuple(list(literal_eval(inpt).values()))
        files_map[get_filename(file, '_Z3_', '.run')] = run_params

def get_kod_params(filename):
    so_far = filename[:filename.rfind('.kod.out')]
    classname, ition, remove_index, check_index, bound = so_far.rsplit('_', 4)
    return classname, ition, int(remove_index) if remove_index != 'None' else -1, int(check_index), int(bound)


def fill_kod_map(kod_results, result_files):
    for file in result_files:
        print('file', file)
        with open(file, 'r') as f:
            try:
                result = literal_eval(f.read())
            except:
                continue
        filename = os.path.basename(file)
        classname, ition, remove_index, check_index, bound = get_kod_params(filename)
        if not classname in kod_results:
            kod_results[classname] = {}
        if not (ition, remove_index, check_index) in kod_results[classname]:
            kod_results[classname][(ition, remove_index, check_index)] = {}
        kod_results[classname][(ition, remove_index, check_index)][bound] = (result['outcome'], result['solving_time'])

def main():
    kod_results_files = [os.path.join(root, f) for root, _, files in os.walk(KOD_RESULTS_DIRECTORY_PATH) for f in files if re.match(r'.*[.]kod[.]out', f)]
    # z3_results_files = [os.path.join(root, f) for root, _, files in os.walk(Z3_RESULTS_DIRECTORY_PATH) for f in files if re.match(r'.*[.]z3[.]out', f)]
    # run_files = [os.path.join(root, f) for root, _, files in os.walk(Z3_RESULTS_DIRECTORY_PATH) for f in files if re.match(r'.*[.]run', f)]
    # params_map = {}
    # fill_params_map(params_map, run_files)
    kod_results = {}
    fill_kod_map(kod_results, kod_results_files)
    for file_results in kod_results.values(): # for every file
        fig, ax = plt.subplots(len(file_results.keys()))
        for i, (params, results) in enumerate(file_results.items()): # for every transition, remove_index, check_index
            ax[i + 1].scatter(params, results[i + 1][1])
            if len(results) != 1:
                ax[i + 1].scatter(params, results[len(results) - 1])
                plt.show()






if __name__ == '__main__':
    main()