import sys
import re

def extract_phase_chars(f):
    phases_to_chars = {}
    phase_name = None
    for line in f:
        if 'updr ended' in line:
            break
        res = re.match('summary of (.+):', line)
        if res:
            phase_name = res.group(1)
            phases_to_chars[phase_name] = []
        else:
            phases_to_chars[phase_name].append(line)

    return phases_to_chars


def phase_stats(chars_lst):
    chars_info = []
    for char in chars_lst:
        num_quantifiers = char.count(':')
        num_literals = char.count('&') + 1
        chars_info.append((num_quantifiers, num_literals))
    return chars_info


def process_file(f) -> None:
    while f:
        line = f.readline()
        if not line:
            return (None, {})
        if 'considering frame' not in line:
            continue

        frame_considered_line = line
        res_line = f.readline()
        if 'safe but not inductive' in res_line:
            continue

        res = re.search('considering frame (\d+)', frame_considered_line.strip())
        frame_num = int(res.group(1))
        break

    p2c = extract_phase_chars(f)
    pstats = {pname: phase_stats(chars) for pname, chars in p2c.items()}

    return frame_num, pstats

def file_summary(filename):
    with open(filename, 'rt') as f:
        return log_summary(f)

def log_summary(f):
    frame_num, pstats = process_file(f)

    phase_summaries = {}
    for pname, pinfo in pstats.items():
        num_clauses = len(pinfo)
        sum_quantifiers = sum(cinfo[0] for cinfo in pinfo)
        sum_literals = sum(cinfo[1] for cinfo in pinfo)
        phase_summaries[pname] = (num_clauses, sum_quantifiers, sum_literals)

    return frame_num, phase_summaries

def sum_list(lst):
    return '%d-%d' % (min(lst), max(lst))

def mean(lst):
    return float(sum(lst)) / len(lst)

def per_phase_stats(pstats):
    pnames = list(pstats[0].keys())
    per_phase_mean_clauses = {pname: mean([pstat[pname][0] for pstat in pstats]) for pname in pnames}
    per_phase_mean_quantifiers = {pname: mean([pstat[pname][1] for pstat in pstats]) for pname in pnames}
    per_phase_mean_literals = {pname: mean([pstat[pname][2] for pstat in pstats]) for pname in pnames}

    return (per_phase_mean_clauses,
            per_phase_mean_quantifiers,
            per_phase_mean_literals)    

def main() -> None:
    if len(sys.argv) < 2:
        print('expected list of filenames')
        sys.exit(1)

    files_lst = sys.argv[1:]
    print("Analyzing ", files_lst)
    summaries = [file_summary(filename) for filename in files_lst]
    summaries = [summary for summary in summaries if (summary[0] is not None)]
    # for summary in summaries:
    #     print(summary)
    # assert False

    ind_frame = sum_list([summary[0] for summary in summaries])
    print('inductive frame: %s' % ind_frame)

    pstats = [summary[1] for summary in summaries]
    per_phase_mean_clauses, per_phase_mean_quantifiers,  per_phase_mean_literals = per_phase_stats(pstats)

    print('mean num clauses: %s' % sum_list(list(per_phase_mean_clauses.values())))
    print('mean num quantifiers: %s' % sum_list(list(per_phase_mean_quantifiers.values())))
    print('mean num literals: %s' % sum_list(list(per_phase_mean_literals.values())))

if __name__ == '__main__':
    main()