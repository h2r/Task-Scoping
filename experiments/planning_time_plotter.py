from matplotlib import pyplot as plt
import numpy as np


def errorfill(x, y, yerr, color=None, alpha_fill=0.3, ax=None, linestyle=None, plt_label=None, marker=None, alpha=None, linewidth=None):
    ax = ax if ax is not None else plt.gca()
    # if color is None:
    #     color = ax._get_lines.color_cycle.next()
    if np.isscalar(yerr) or len(yerr) == len(y):
        ymin = y - yerr
        ymax = y + yerr
    elif len(yerr) == 2:
        ymin, ymax = yerr
    #ax.errorbar(x, y, yerr=yerr, ecolor=color, label=plt_label)
    ax.plot(x, y, color=color, label=plt_label, linestyle=linestyle, marker=marker, alpha=alpha, linewidth=linewidth)
    #ax.errorbar(x, y, yerr = ymax - y, label=plt_label, linestyle=linestyle, color=color)
    ax.fill_between(x, ymax, ymin, color=color, alpha=alpha_fill)

def plot():
    plt.figure(1)

    domain_num = np.log10(np.array([16.0*(10 ** 32),10.24*(10 ** 34),65.546 * (10 ** 35),41.943 * (10 ** 37),26.844 * (10 ** 39)]))

    planner_time = np.array([8.38, 13.0, 19.2, 27.6, 38.7])
    planner_stddev = np.array([0.3,0.4,0.3,0.8,0.7])
    planner_with_error = [planner_time - planner_stddev, planner_time + planner_stddev]

    planner_and_scoper_time = np.array([6.91,7.30,7.37,8.12,8.53])
    planner_and_scoper_stddev = np.array([0.07,0.08,0.2,0.05,0.04])
    pands_with_error = [planner_and_scoper_time - planner_and_scoper_stddev, planner_and_scoper_time + planner_and_scoper_stddev]

    errorfill(domain_num, planner_time, yerr=planner_with_error, color='red', linestyle='-', plt_label='ENHSP-2020', marker='o')
    errorfill(domain_num, planner_and_scoper_time, yerr=pands_with_error, color='blue', linestyle='-', plt_label='TS (ours) + ENHSP-2020', marker = 'o')

    plt.xlabel('Log size of domain (base 10)')
    plt.ylabel('Wall clock time taken to find plan/s')
    plt.title('Planning time vs. log. domain size')
#    plt.legend(bbox_to_anchor=(1.05, 1), loc='upper left', borderaxespad=0.)
    plt.legend()

    plt.show()

if __name__ == '__main__':
    plot()