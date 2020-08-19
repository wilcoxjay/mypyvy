import os
import re
import multiprocessing as mp

EXAMPLES_DIRECTORY_PATH = '/Users/amohamdy/stanford/aiken-1920-research/mypyvy/examples'

def run_kod_on(filepath: str, bound: int):
    return filepath, bound

def main():
    test_files = [os.path.join(root, f) for root, _, files in os.walk(EXAMPLES_DIRECTORY_PATH) for f in files if re.match('.*\.pyv', f)]
    pool = mp.Pool(mp.cpu_count())
    results = pool.starmap(run_kod_on, [(f, b) for b in range(1, 3) for f in test_files])
    pool.close()


if __name__ == '__main__':
    main()