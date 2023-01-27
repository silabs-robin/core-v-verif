import sys
import os
import argparse
import subprocess
import yaml
import shlex

if (sys.version_info < (3,0,0)):
    print ('Requires python 3')
    exit(1)

supported_cores = ["cv32e40s", "cv32e40x"]

try:
    default_core = os.environ['CV_CORE']
except KeyError:
    default_core = 'None'

topdir = os.path.abspath(os.path.join(os.path.dirname(os.path.realpath(__file__)), '..'))
parser = argparse.ArgumentParser()
parser.add_argument("--dry_run",                help="Prints generated yaml to stdout",   action="store_true")
parser.add_argument("--core",                   help="Set the core to generate test for", choices=supported_cores)
parser.add_argument("--pmp_num_regions",        help="Set number of Pmp regions",         type=str, default="0")
parser.add_argument("--mhpmcounter_num",        help="Set number of mhpmcounters",        type=str, default="3")
parser.add_argument("--num_triggers",           help="Set number of trigger registers",   type=str, default="1")
parser.add_argument("--clic_enable",            help="Enable clic support",               action="store_true", default=False)
parser.add_argument("--zc_enable",              help="Enable Zc support",                 action="store_true", default=False)
parser.add_argument("--clint_enable",           help="Enable Basic Interrupts",           action="store_true", default=False)
parser.add_argument("--debug_enable",           help="Enable Debug Registers",            action="store_true", default=False)
parser.add_argument("--m_ext_enable",           help="Enable M extension",                action="store_true", default=False)
parser.add_argument("--m_none_enable",          help="Disable M extension",               action="store_true", default=False)
parser.add_argument("--i_ext_enable",           help="Enable I extension",                action="store_true", default=False)
parser.add_argument("--e_ext_enable",           help="Enable E extension",                action="store_true", default=False)
parser.add_argument("--xsecure_enable",         help="Enable Xsecure Registers",            action="store_true", default=False)
parser.add_argument("--output",                 help="Output path",                       type=str)
parser.add_argument("--iterations",             help="Number of generated tests",         type=str, default="1")

args = parser.parse_args()

if (args.core == None or args.core not in supported_cores):
    print("Error: No core supported core specified")
    exit(1)
if (args.output == None):
    print("Error: no output path")
    exit(1)
if int(args.pmp_num_regions) not in range(65):
    print("Error: unsupported number of regions setting")
    exit(1)

if args.dry_run:
    print('{}'.format(args))

script_path      = os.path.join(topdir, '{}/vendor_lib/google/riscv-dv/scripts/gen_csr_test.py'.format(args.core.lower()))
yaml_file_path   = os.path.join(topdir, '{}'.format(args.core.lower()) + '/env/corev-dv/{}'.format(args.core.lower()) + '_csr_template.yaml')
template_path    = os.path.join(topdir, './bin/templates/csr_access_test_template.S')
output_yaml_path = ""

def run_riscv_dv_gen_csr_script(output_yaml_path):
    try:
        print("riscv-dv script path: {}".format(script_path))
        print("csr description used: {}".format(output_yaml_path))
        script_args = { "csr_file"   : ' --csr_file {}'.format(output_yaml_path),
                        "xlen"       : ' --xlen 32',
                        "out"        : ' --out ' + args.output,
                        "iterations" : ' --iterations ' + args.iterations}
        subprocess.call(shlex.split("python3 " + script_path + script_args["csr_file"] + script_args["xlen"] + script_args["out"] + script_args["iterations"]))
    except Exception as e:
        print(e)

def preprocess_yaml():
    input_script_path = yaml_file_path
    w_enable = True
    w_enable_n = w_enable
    str_args = ""
    enabled_features = {
      "clic":         False,
      "clint":        False,
      "debug":        False,
      "e_ext":        False,
      "i_ext":        False,
      "m_ext":        False,
      "m_none":       False,
      "readonly":     False,
      "xsecure":      False,
      "zc":           False,
      "mhpmcounters": 0,
      "pmp":          0,
      "trigger":      0,
      }

    # CLIC
    if (args.clic_enable):
        str_args = str_args + "_clic"
        enabled_features["clic"] = True
    # CLINT
    if (args.clint_enable or not args.clic_enable):
        str_args = str_args + "_clint"
        enabled_features["clint"] = True if not enabled_features["clic"] else False
    # DEBUG
    if (args.debug_enable):
        str_args = str_args + "_debug"
        enabled_features["debug"] = True
    # I/E
    if (args.i_ext_enable):
        str_args = str_args + "_i"
        enabled_features["i_ext"] = True
    elif (args.e_ext_enable):
        str_args = str_args + "_e"
        enabled_features["e_ext"] = True
    else:
        print("error: must have 'i_ext' or 'e_ext'", file=sys.stderr)
        exit(1)
    # M
    if (args.m_ext_enable):
        str_args = str_args + "_m"
        enabled_features["m_ext"] = True
    elif (args.m_none_enable):
        str_args = str_args + "_mnone"
        enabled_features["m_none"] = True
    else:
        print("error: must have 'm_ext' or 'm_none'", file=sys.stderr)
        exit(1)
    # XSECURE
    if (args.xsecure_enable):
        str_args = str_args + "_xsecure"
        enabled_features["xsecure"] = True
    # ZC
    if (args.zc_enable):
        str_args = str_args + "_zc"
        enabled_features["zc"] = True
    # MHPMCOUNTERS
    if (int(args.mhpmcounter_num) > 0):
        str_args = str_args + "_mhpmctr" + args.mhpmcounter_num
        enabled_features["mhpmcounters"] = int(args.mhpmcounter_num)
    # PMP
    if (int(args.pmp_num_regions) > 0):
        str_args = str_args + "_pmp" + args.pmp_num_regions
        enabled_features["pmp"] = int(args.pmp_num_regions)
    # TRIGGERS
    if (int(args.num_triggers) > 0):
        str_args = str_args + "_triggers" + args.num_triggers
        enabled_features["trigger"] = int(args.num_triggers)
    # TODO:silabs-robin Any other "enabled_features"?

    print("enabled_features: {}".format(enabled_features))

    output_script_path = os.path.join(args.output) + "{}_csr_template.yaml".format(args.core.lower() + str_args)
    if not args.dry_run:
        output_script_handle = open(output_script_path, "w")

    input_script_handle = open(input_script_path, "r")
    input_script_lines = input_script_handle.readlines()
    for line in input_script_lines:
        input_list = line.split()
        # Cond <true/false>
        if len(input_list) == 3 and input_list[0] == "###" and input_list[1].lower() == "cond":
            if not enabled_features[input_list[2].lower()]:
                w_enable   = False
                w_enable_n = False
        # Cond <key pair>
        elif len(input_list) == 4 and input_list[0] == "###" and input_list[1].lower() == "cond":
            if (int(input_list[3].lower()) > int(enabled_features[input_list[2].lower()])):
                w_enable   = False
                w_enable_n = False
            else:
                w_enable_n = True
                w_enable   = True
        # Endcond
        elif len(input_list) == 2 and input_list[0] == "###" and input_list[1].lower() == "endcond":
            w_enable_n = True
        if w_enable == True:
            if args.dry_run:
                print(line.strip("\n"))
            else:
                output_script_handle.write(line)
        if w_enable == False:
            w_enable = w_enable_n

    if not args.dry_run:
        output_script_handle.close()
    input_script_handle.close()
    return output_script_path

def gen_riscv_dv_gen_csr_file(iteration = 1):
    try:
        template_handle = open(template_path, "r")
        tlines = template_handle.readlines()

        file_handle = open(os.path.join(args.output) + "riscv_csr_test_{}.S".format(iteration), "r")
        lines = file_handle.readlines()
        file_handle.close()

        file_handle = open(os.path.join(args.output) + "riscv_csr_test_{}.S".format(iteration), "w")
        write_next = 0
        twrite_next = 0
        for line in lines:
            if write_next == 1 and line.strip("\n") != "csr_pass:":
                file_handle.write(line)
            elif line.strip("\n") == "_start:":
                for tline in tlines:
                    if tline.strip("\n") != "_start0:":
                        file_handle.write(tline)
                    elif tline.strip("\n") == "_start0:":
                        file_handle.write(tline)
                        break
                write_next = 1;
            elif line.strip("\n") == "csr_pass:":
                write_next = 0;
                for tline in tlines:
                    if tline.strip("\n") == "_start0:" and twrite_next == 0:
                        twrite_next = 1
                    elif twrite_next == 1:
                        file_handle.write(tline)
                break
        file_handle.close()
        template_handle.close()
    except Exception as e:
        print(e)

if args.dry_run:
    preprocess_yaml()
else:
    run_riscv_dv_gen_csr_script(preprocess_yaml())
    for iteration in range(int(args.iterations)):
        gen_riscv_dv_gen_csr_file(iteration)