import os
import sys
import re
from ast import literal_eval

KOD_RESULTS_DIRECTORY_PATH = '/Users/amohamdy/stanford/aiken-1920-research/mypyvy/_kod_files/_KOD_RESULTS/'
Z3_RESULTS_DIRECTORY_PATH = '/Users/amohamdy/stanford/aiken-1920-research/mypyvy/_z3_files/'
'''
{
    'lockserv': {
        ('request_msg', 1, 0): (unsat, 3ms)
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

def fill_kod_map(kod_results, result_files, params_map):
    for file in result_files:
        print('file', file)
        with open(file, 'r') as f:
            result = literal_eval(f.read())
        filename = get_filename(file, '_KOD_', '.result')
        basename = filename[:filename.rfind('_')]

        if basename in params_map:
            params = params_map[basename]
        else:
            print(f'File not found in params_map {file}')
            continue
        # classname = re.split('\d+', basename, 1)[0][:-1] # First part without the trailing '_'
        classname = basename[:filename.rfind('_')]
        kod_results[classname] = params

def main():
    kod_results_files = [os.path.join(root, f) for root, _, files in os.walk(KOD_RESULTS_DIRECTORY_PATH) for f in files if re.match(r'.*[.]result', f)]
    z3_results_files = [os.path.join(root, f) for root, _, files in os.walk(Z3_RESULTS_DIRECTORY_PATH) for f in files if re.match(r'.*[.]z3[.]out', f)]
    run_files = [os.path.join(root, f) for root, _, files in os.walk(Z3_RESULTS_DIRECTORY_PATH) for f in files if re.match(r'.*[.]run', f)]
    params_map = {}
    fill_params_map(params_map, run_files)
    kod_results = {}
    fill_kod_map(kod_results, kod_results_files, params_map)
    print('kod_results:', kod_results)

    # print('map: ', files_map)

if __name__ == '__main__':
    main()