import os
import sys
import re
import matplotlib.pyplot as plt
from ast import literal_eval

KOD_RESULTS_DIRECTORY_PATH = '_KOD_RESULTS/'
Z3_RESULTS_DIRECTORY_PATH = '_Z3_RESULTS/'
'''
kod_results is something like this:
{
    'lockserv':
    {
        ('request_msg', 1, 0):
        {
            1: (unsat, 3ms),
            2: (unsat, 5ms),
            3: (sat, 2ms)
        }
        ...
    }
    ...
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
    classname, ition, remove_index, check_index, bound = so_far.rsplit('__', 4)
    return classname, ition, int(remove_index) if remove_index != 'None' else -1, int(check_index), int(bound)


def fill_kod_map(kod_results, result_files):
    for file in result_files:
        print('file', file)
        with open(file, 'r') as f:
            try:
                result = literal_eval(f.read())
            except:
                print('ERROR reading file')
                continue
        filename = os.path.basename(file)
        classname, ition, remove_index, check_index, bound = get_kod_params(filename)
        if not classname in kod_results:
            kod_results[classname] = {}
        if not (ition, remove_index, check_index) in kod_results[classname]:
            kod_results[classname][(ition, remove_index, check_index)] = {}
        kod_results[classname][(ition, remove_index, check_index)][bound] = (result['outcome'], result['solving_time'] + result['translation_time'])

#def main():
if __name__ == '__main__':
    kod_results_files = [os.path.join(root, f) for root, _, files in os.walk(KOD_RESULTS_DIRECTORY_PATH) for f in files if re.match(r'.*[.]kod[.]out', f)]
    # z3_results_files = [os.path.join(root, f) for root, _, files in os.walk(Z3_RESULTS_DIRECTORY_PATH) for f in files if re.match(r'.*[.]z3[.]out', f)]
    # run_files = [os.path.join(root, f) for root, _, files in os.walk(Z3_RESULTS_DIRECTORY_PATH) for f in files if re.match(r'.*[.]run', f)]
    # params_map = {}
    # fill_params_map(params_map, run_files)
    kod_results = {}
    fill_kod_map(kod_results, kod_results_files)
    fig, ax = plt.subplots(len(kod_results.keys()))
    for i, (filename, file_results) in enumerate(kod_results.items()): # for every file
        x = []
        y = []
        res = []
        for params, results in file_results.items(): # for every transition, remove_index, check_index
            total_time = sum(t for _, t in results.values())
            y.append(total_time)
        # should probably sort?
        plt.figure()
        plt.plot(y, 'o')
        # plt.show()
        plt.savefig(f'{filename}.png')
        # ax[i].plot(x, y)
        # fig.show()
        # fig.savefig("example_fig")
    x = []
    y = []
    for r in kod_results.values():
        for rr in r.values():
            for bound, (res, t) in rr.items():
                if res == 'UNSATISFIABLE':
                    x.append(bound)
                    y.append(t)
    plt.figure()
    plt.plot(x, y, 'o')
    x = []
    y = []
    for r in kod_results.values():
        for rr in r.values():
            for bound, (res, t) in rr.items():
                if res == 'SATISFIABLE':
                    x.append(bound)
                    y.append(t)
    plt.plot(x, y, 'o')
    plt.savefig('bound.png')