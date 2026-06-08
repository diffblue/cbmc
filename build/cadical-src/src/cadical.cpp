/*------------------------------------------------------------------------*/

// Do include 'internal.hpp' but try to minimize internal dependencies.

#include "internal.hpp"
#include "signal.hpp" // Separate, only need for apps.

/*------------------------------------------------------------------------*/

namespace CaDiCaL {

// A wrapper app which makes up the CaDiCaL stand alone solver.  It in
// essence only consists of the 'App::main' function.  So this class
// contains code, which is not required if only the library interface in
// the class 'Solver' is used (defined in 'cadical.hpp').  It further uses
// static data structures in order to have a signal handler catch signals.
//
// It is thus neither thread-safe nor reentrant.  If you want to use
// multiple instances of the solver use the 'Solver' interface directly
// which is thread-safe and reentrant among different solver instances.

/*------------------------------------------------------------------------*/

class App : public Handler, public Terminator {

  Solver *solver; // Global solver.

#ifndef _WIN32
  // Command line options.
  //
  int time_limit; // '-t <sec>'
#endif

  // Strictness of (DIMACS) parsing:
  //
  //  0 = force parsing and completely ignore header
  //  1 = relaxed header handling (default)
  //  2 = strict header handling
  //
  // To use '0' use '-f' of '--force'.
  // To use '2' use '--strict'.
  //
  int force_strict_parsing;

  bool force_writing;
  static bool most_likely_existing_cnf_file (const char *path);

  // Internal variables.
  //
  int max_var;           // Set after parsing.
  volatile bool timesup; // Asynchronous termination.

  // Printing.
  //
  void print_usage (bool all = false);
  void print_witness (FILE *);

#ifndef QUIET
  void signal_message (const char *msg, int sig);
#endif

  // Option handling.
  //
  bool set (const char *);
  bool set (const char *, int);
  int get (const char *);
  bool verbose () { return get ("verbose") && !get ("quiet"); }

  /*----------------------------------------------------------------------*/

  // The actual initialization.
  //
  void init ();

  // Terminator interface.
  //
  bool terminate () { return timesup; }

  // Handler interface.
  //
  void catch_signal (int sig);
  void catch_alarm ();

public:
  App ();
  ~App ();

  // Parse the arguments and run the solver.
  //
  int main (int arg, char **argv);
};

/*------------------------------------------------------------------------*/

// clang-format off

void App::print_usage (bool all) {
  printf (

"usage: cadical [ <option> ... ] [ <input> [ <proof> ] ]\n"
"\n"
"where '<option>' is one of the following common options:\n"
"\n"
         );

  if (!all) { // Print only a short list of common options.
    printf (

"  -h             print this short list of common options\n"
"  --help         print complete list of all options\n"
"  --version      print version\n"
"\n"
"  -n             do not print witness\n"
#ifndef QUIET
"  -v             increase verbosity\n"
"  -q             be quiet\n"
#endif
"\n"
#ifndef _WIN32
"  -t <sec>       set wall clock time limit\n"
#endif

           );
  } else { // Print complete list of all options.
    printf (

"  -h             print alternatively only a list of common options\n"
"  --help         print this complete list of all options\n"
"  --version      print version\n"
"\n"
"  -n             do not print witness (same as '--no-witness')\n"
#ifndef QUIET
"  -v             increase verbosity (see also '--verbose' below)\n"
"  -q             be quiet (same as '--quiet')\n"
#endif
#ifndef _WIN32
"  -t <sec>       set wall clock time limit\n"
#endif
"\n"
"Or '<option>' is one of the less common options\n"
"\n"
"  -L<rounds>     run local search initially (default '0' rounds)\n"
"  -O<level>      increase limits by '2^<level>' or '10^<level>'\n"
"  -P<rounds>     initial preprocessing (default '0' rounds)\n"
"\n"
"Note there is no separating space for the options above while the\n"
"following options require a space after the option name:\n"
"\n"
"  -c <limit>     limit the number of conflicts (default unlimited)\n"
"  -d <limit>     limit the number of decisions (default unlimited)\n"
"\n"
"  -o <output>    write simplified CNF in DIMACS format to file\n"
"  -e <extend>    write reconstruction/extension stack to file\n"
#ifdef LOGGING
"  -l             enable logging messages (same as '--log')\n"
#endif
"\n"
"  --force | -f   parsing broken DIMACS header and writing proofs\n"
"  --strict       strict parsing (no white space in header)\n"
"\n"
"  -r <sol>       read solution in competition output format\n"
"                 to check consistency of learned clauses\n"
"                 during testing and debugging\n"
"\n"
"  -w <sol>       write result including a potential witness\n"
"                 solution in competition format to the given "
"file\n"
"\n"
"  --colors       force colored output\n"
"  --no-colors    disable colored output to terminal\n"
"  --no-witness   do not print witness (see also '-n' above)\n"
"\n"
"  --build        print build configuration\n"
"  --copyright    print copyright information\n");

    printf (

"\n"
"There are pre-defined configurations of advanced internal options:\n"
"\n"

	    );

    solver->configurations ();

    printf (
"\n"
"Or '<option>' is one of the following advanced internal options:\n"
"\n"
	);

    solver->usage ();

    printf (

"\n"
"The internal options have their default value printed in brackets\n"
"after their description.  They can also be used in the form\n"
"'--<name>' which is equivalent to '--<name>=1' and in the form\n"
"'--no-<name>' which is equivalent to '--<name>=0'.  One can also\n"
"use 'true' instead of '1', 'false' instead of '0', as well as\n"
"numbers with positive exponent such as '1e3' instead of '1000'.\n"
"\n"
"Alternatively option values can also be specified in the header\n"
"of the DIMACS file, e.g., 'c --elim=false', or through environment\n"
"variables, such as 'CADICAL_ELIM=false'.  The embedded options in\n"
"the DIMACS file have highest priority, followed by command line\n"
"options and then values specified through environment variables.\n"

           );
  }

  //------------------------------------------------------------------------
  // Common to both complete and common option usage.

  printf (

"\n"
"The input is read from '<input>' assumed to be in DIMACS format.\n"
"Incremental 'p inccnf' files are supported too with cubes at the end.\n"
"If '<proof>' is given then a DRAT proof is written to that file.\n"

         );

  //------------------------------------------------------------------------
  // More explanations for complete option usage.

  if (all) {
    printf (

"\n"
"If '<input>' is missing then the solver reads from '<stdin>',\n"
"also if '-' is used as input path name '<input>'.  Similarly,\n"
"\n"
"For incremental files each cube is solved in turn. The solver\n"
"stops at the first satisfied cube if there is one and uses that\n"
"one for the witness to print.  Conflict and decision limits are\n"
"applied to each individual cube solving call while '-P', '-L'"
#ifdef _WIN32
"\n"
#else
" and\n"
"'-t' "
#endif
"remain global.  Only if all cubes were unsatisfiable the solver\n"
"prints the standard unsatisfiable solution line ('s UNSATISFIABLE').\n"
"\n"
"By default the proof is stored in the binary DRAT format unless\n"
"the option '--no-binary' is specified or the proof is written\n"
"to '<stdout>' and '<stdout>' is connected to a terminal.\n"
"\n"
"The input is assumed to be compressed if it is given explicitly\n"
"and has a '.gz', '.bz2', '.xz' or '.7z' suffix.  The same applies\n"
"to the output file.  In order to use compression and decompression\n"
"the corresponding utilities 'gzip', 'bzip', 'xz', and '7z' (depending\n"
"on the format) are required and need to be installed on the system.\n"
"The solver checks file type signatures though and falls back to\n"
"non-compressed file reading if the signature does not match.\n"

           );
  }
}

// clang-format on

/*------------------------------------------------------------------------*/

// Pretty print competition format witness with 'v' lines.

void App::print_witness (FILE *file) {
  int c = 0, i = 0, tmp;
  do {
    if (!c)
      fputc ('v', file), c = 1;
    if (i++ == max_var)
      tmp = 0;
    else if (solver->external->ervars[i])
      continue;
    else
      tmp = solver->val (i) < 0 ? -i : i;
    char str[32];
    snprintf (str, sizeof str, " %d", tmp);
    int l = strlen (str);
    if (c + l > 78)
      fputs ("\nv", file), c = 1;
    fputs (str, file);
    c += l;
  } while (tmp);
  if (c)
    fputc ('\n', file);
}

/*------------------------------------------------------------------------*/

// Wrapper around option setting.

int App::get (const char *o) { return solver->get (o); }
bool App::set (const char *o, int v) { return solver->set (o, v); }
bool App::set (const char *arg) { return solver->set_long_option (arg); }

/*------------------------------------------------------------------------*/

bool App::most_likely_existing_cnf_file (const char *path) {
  if (!File::exists (path))
    return false;

  if (has_suffix (path, ".dimacs"))
    return true;
  if (has_suffix (path, ".dimacs.gz"))
    return true;
  if (has_suffix (path, ".dimacs.xz"))
    return true;
  if (has_suffix (path, ".dimacs.bz2"))
    return true;
  if (has_suffix (path, ".dimacs.7z"))
    return true;
  if (has_suffix (path, ".dimacs.lzma"))
    return true;

  if (has_suffix (path, ".cnf"))
    return true;
  if (has_suffix (path, ".cnf.gz"))
    return true;
  if (has_suffix (path, ".cnf.xz"))
    return true;
  if (has_suffix (path, ".cnf.bz2"))
    return true;
  if (has_suffix (path, ".cnf.7z"))
    return true;
  if (has_suffix (path, ".cnf.lzma"))
    return true;

  return false;
}

/*------------------------------------------------------------------------*/

// Short-cut for errors to avoid a hard 'exit'.

#define APPERR(...) \
  do { \
    solver->error (__VA_ARGS__); \
  } while (0)

/*------------------------------------------------------------------------*/

int App::main (int argc, char **argv) {

  // Handle options which lead to immediate exit first.

  if (argc == 2) {
    const char *arg = argv[1];
    if (!strcmp (arg, "-h")) {
      print_usage ();
      return 0;
    } else if (!strcmp (arg, "--help")) {
      print_usage (true);
      return 0;
    } else if (!strcmp (arg, "--version")) {
      printf ("%s\n", CaDiCaL::version ());
      return 0;
    } else if (!strcmp (arg, "--build")) {
      tout.disable ();
      Solver::build (stdout, "");
      return 0;
    } else if (!strcmp (arg, "--copyright")) {
      printf ("%s\n", copyright ());
      printf ("%s\n", authors ());
      printf ("%s\n", affiliations ());
      return 0;
    }
  }

  // Now initialize solver.

  init ();

  // Set all argument option values to not used yet.

  const char *preprocessing_specified = 0, *optimization_specified = 0;
  const char *read_solution_path = 0, *write_result_path = 0;
  const char *dimacs_path = 0, *proof_path = 0;
  bool proof_specified = false, dimacs_specified = false;
  int optimize = 0, preprocessing = 0, localsearch = 0;
  const char *output_path = 0, *extension_path = 0;
  int conflict_limit = -1, decision_limit = -1;
  const char *conflict_limit_specified = 0;
  const char *decision_limit_specified = 0;
  const char *localsearch_specified = 0;
#ifndef __MINGW32__
  const char *time_limit_specified = 0;
#endif
  bool witness = true, less = false, status = true;
  const char *dimacs_name, *err;

  for (int i = 1; i < argc; i++) {
    if (!strcmp (argv[i], "-h") || !strcmp (argv[i], "--help") ||
        !strcmp (argv[i], "--build") || !strcmp (argv[i], "--version") ||
        !strcmp (argv[i], "--copyright")) {
      APPERR ("can only use '%s' as single first option", argv[i]);
    } else if (!strcmp (argv[i], "-")) {
      if (proof_specified)
        APPERR ("too many arguments");
      else if (!dimacs_specified)
        dimacs_specified = true;
      else
        proof_specified = true;
    } else if (!strcmp (argv[i], "-r")) {
      if (++i == argc)
        APPERR ("argument to '-r' missing");
      else if (read_solution_path)
        APPERR ("multiple read solution file options '-r %s' and '-r %s'",
                read_solution_path, argv[i]);
      else
        read_solution_path = argv[i];
    } else if (!strcmp (argv[i], "-w")) {
      if (++i == argc)
        APPERR ("argument to '-w' missing");
      else if (write_result_path)
        APPERR ("multiple solution file options '-w %s' and '-w %s'",
                write_result_path, argv[i]);
      else
        write_result_path = argv[i];
    } else if (!strcmp (argv[i], "-o")) {
      if (++i == argc)
        APPERR ("argument to '-o' missing");
      else if (output_path)
        APPERR ("multiple output file options '-o %s' and '-o %s'",
                output_path, argv[i]);
      else if (!force_writing && most_likely_existing_cnf_file (argv[i]))
        APPERR ("output file '%s' most likely existing CNF (use '-f')",
                argv[i]);
      else if (!File::writable (argv[i]))
        APPERR ("output file '%s' not writable", argv[i]);
      else
        output_path = argv[i];
    } else if (!strcmp (argv[i], "-e")) {
      if (++i == argc)
        APPERR ("argument to '-e' missing");
      else if (extension_path)
        APPERR ("multiple extension file options '-e %s' and '-e %s'",
                extension_path, argv[i]);
      else if (!force_writing && most_likely_existing_cnf_file (argv[i]))
        APPERR ("extension file '%s' most likely existing CNF (use '-f')",
                argv[i]);
      else if (!File::writable (argv[i]))
        APPERR ("extension file '%s' not writable", argv[i]);
      else
        extension_path = argv[i];
    } else if (is_color_option (argv[i])) {
      tout.force_colors ();
      terr.force_colors ();
    } else if (is_no_color_option (argv[i])) {
      tout.force_no_colors ();
      terr.force_no_colors ();
    } else if (!strcmp (argv[i], "--witness") ||
               !strcmp (argv[i], "--witness=true") ||
               !strcmp (argv[i], "--witness=1"))
      witness = true;
    else if (!strcmp (argv[i], "-n") || !strcmp (argv[i], "--no-witness") ||
             !strcmp (argv[i], "--witness=false") ||
             !strcmp (argv[i], "--witness=0"))
      witness = false;
    else if (!strcmp (argv[i], "--status") ||
             !strcmp (argv[i], "--status=true") ||
             !strcmp (argv[i], "--status=1"))
      status = true;
    else if (!strcmp (argv[i], "-n") || !strcmp (argv[i], "--no-status") ||
             !strcmp (argv[i], "--status=false") ||
             !strcmp (argv[i], "--status=0"))
      status = false;
    else if (!strcmp (argv[i], "--less")) { // EXPERIMENTAL!
      if (less)
        APPERR ("multiple '--less' options");
      else if (!isatty (1))
        APPERR ("'--less' without '<stdout>' connected to terminal");
      else
        less = true;
    } else if (!strcmp (argv[i], "-c")) {
      if (++i == argc)
        APPERR ("argument to '-c' missing");
      else if (conflict_limit_specified)
        APPERR ("multiple conflict limits '-c %s' and '-c %s'",
                conflict_limit_specified, argv[i]);
      else if (!parse_int_str (argv[i], conflict_limit))
        APPERR ("invalid argument in '-c %s'", argv[i]);
      else if (conflict_limit < 0)
        APPERR ("invalid conflict limit");
      else
        conflict_limit_specified = argv[i];
    } else if (!strcmp (argv[i], "-d")) {
      if (++i == argc)
        APPERR ("argument to '-d' missing");
      else if (decision_limit_specified)
        APPERR ("multiple decision limits '-d %s' and '-d %s'",
                decision_limit_specified, argv[i]);
      else if (!parse_int_str (argv[i], decision_limit))
        APPERR ("invalid argument in '-d %s'", argv[i]);
      else if (decision_limit < 0)
        APPERR ("invalid decision limit");
      else
        decision_limit_specified = argv[i];
    }
#ifndef _WIN32
    else if (!strcmp (argv[i], "-t")) {
      if (++i == argc)
        APPERR ("argument to '-t' missing");
      else if (time_limit_specified)
        APPERR ("multiple time limit '-t %s' and '-t %s'",
                time_limit_specified, argv[i]);
      else if (!parse_int_str (argv[i], time_limit))
        APPERR ("invalid argument in '-d %s'", argv[i]);
      else if (time_limit < 0)
        APPERR ("invalid time limit");
      else
        time_limit_specified = argv[i];
    }
#endif
#ifndef QUIET
    else if (!strcmp (argv[i], "-q"))
      set ("--quiet");
    else if (!strcmp (argv[i], "-v"))
      set ("verbose", get ("verbose") + 1);
#endif
#ifdef LOGGING
    else if (!strcmp (argv[i], "-l"))
      set ("--log");
#endif
    else if (!strcmp (argv[i], "-f") || !strcmp (argv[i], "--force") ||
             !strcmp (argv[i], "--force=1") ||
             !strcmp (argv[i], "--force=true"))
      force_strict_parsing = 0, force_writing = true;
    else if (!strcmp (argv[i], "--strict") ||
             !strcmp (argv[i], "--strict=1") ||
             !strcmp (argv[i], "--strict=true"))
      force_strict_parsing = 2;
    else if (has_prefix (argv[i], "-O")) {
      if (optimization_specified)
        APPERR ("multiple optimization options '%s' and '%s'",
                optimization_specified, argv[i]);
      optimization_specified = argv[i];
      if (!parse_int_str (argv[i] + 2, optimize))
        APPERR ("invalid optimization option '%s'", argv[i]);
      if (optimize < 0 || optimize > 31)
        APPERR ("invalid argument in '%s' (expected '0..31')", argv[i]);
    } else if (has_prefix (argv[i], "-P")) {
      if (preprocessing_specified)
        APPERR ("multiple preprocessing options '%s' and '%s'",
                preprocessing_specified, argv[i]);
      preprocessing_specified = argv[i];
      if (!parse_int_str (argv[i] + 2, preprocessing))
        APPERR ("invalid preprocessing option '%s'", argv[i]);
      if (preprocessing < 0)
        APPERR ("invalid argument in '%s' (expected non-negative number)",
                argv[i]);
    } else if (has_prefix (argv[i], "-L")) {
      if (localsearch_specified)
        APPERR ("multiple local search options '%s' and '%s'",
                localsearch_specified, argv[i]);
      localsearch_specified = argv[i];
      if (!parse_int_str (argv[i] + 2, localsearch))
        APPERR ("invalid local search option '%s'", argv[i]);
      if (localsearch < 0)
        APPERR ("invalid argument in '%s' (expected non-negative number)",
                argv[i]);
    } else if (has_prefix (argv[i], "--") &&
               solver->is_valid_configuration (argv[i] + 2)) {
      solver->configure (argv[i] + 2);
    } else if (set (argv[i])) {
      /* nothing do be done */
    } else if (argv[i][0] == '-')
      APPERR ("invalid option '%s'", argv[i]);
    else if (proof_specified)
      APPERR ("too many arguments");
    else if (dimacs_specified) {
      proof_path = argv[i];
      proof_specified = true;
      if (!force_writing && most_likely_existing_cnf_file (proof_path))
        APPERR ("DRAT proof file '%s' most likely existing CNF (use '-f')",
                proof_path);
      else if (!File::writable (proof_path))
        APPERR ("DRAT proof file '%s' not writable", proof_path);
    } else
      dimacs_specified = true, dimacs_path = argv[i];
  }

  /*----------------------------------------------------------------------*/

  if (dimacs_specified && dimacs_path && !File::exists (dimacs_path))
    APPERR ("DIMACS input file '%s' does not exist", dimacs_path);
  if (read_solution_path && !File::exists (read_solution_path))
    APPERR ("solution file '%s' does not exist", read_solution_path);
  if (dimacs_specified && dimacs_path && proof_specified && proof_path &&
      !strcmp (dimacs_path, proof_path) && strcmp (dimacs_path, "-"))
    APPERR ("DIMACS input file '%s' also specified as DRAT proof file",
            dimacs_path);

  /*----------------------------------------------------------------------*/
  // The '--less' option is not fully functional yet (it is also not
  // mentioned in the 'usage' message yet).  It only works as expected if
  // you let the solver run until it exits.  The goal is to have a similar
  // experience as with 'git diff' if the terminal is too small for the
  // printed messages, but this needs substantial hacking.
  //
  // TODO: add proper forking, waiting, signal catching & propagating ...
  //
  FILE *less_pipe;
  if (less) {
    assert (isatty (1));
    less_pipe = popen ("less -r", "w");
    if (!less_pipe)
      APPERR ("could not execute and open pipe to 'less -r' command");
    dup2 (fileno (less_pipe), 1);
  } else
    less_pipe = 0;

  /*----------------------------------------------------------------------*/

  if (read_solution_path && !get ("check"))
    set ("--check");
#ifndef QUIET
  if (!get ("quiet")) {
    solver->section ("banner");
    solver->message ("%sCaDiCaL SAT Solver%s", tout.bright_magenta_code (),
                     tout.normal_code ());
    solver->message ("%s%s%s", tout.bright_magenta_code (), copyright (),
                     tout.normal_code ());
    solver->message ("%s%s%s", tout.bright_magenta_code (), authors (),
                     tout.normal_code ());
    solver->message ("%s%s%s", tout.bright_magenta_code (), affiliations (),
                     tout.normal_code ());
    solver->message ();
    CaDiCaL::Solver::build (stdout, "c ");
  }
#endif
  if (preprocessing > 0 || localsearch > 0 ||
#ifndef _WIN32
      time_limit >= 0 ||
#endif
      conflict_limit >= 0 || decision_limit >= 0) {
    solver->section ("limit");
    if (preprocessing > 0) {
      solver->message (
          "enabling %d initial rounds of preprocessing (due to '%s')",
          preprocessing, preprocessing_specified);
      solver->limit ("preprocessing", preprocessing);
    }
    if (localsearch > 0) {
      solver->message (
          "enabling %d initial rounds of local search (due to '%s')",
          localsearch, localsearch_specified);
      solver->limit ("localsearch", localsearch);
    }
#ifndef _WIN32
    if (time_limit >= 0) {
      solver->message (
          "setting time limit to %d seconds real time (due to '-t %s')",
          time_limit, time_limit_specified);
      Signal::alarm (time_limit);
      solver->connect_terminator (this);
    }
#endif
    if (conflict_limit >= 0) {
      solver->message (
          "setting conflict limit to %d conflicts (due to '%s')",
          conflict_limit, conflict_limit_specified);
      bool succeeded = solver->limit ("conflicts", conflict_limit);
      assert (succeeded), (void) succeeded;
    }
    if (decision_limit >= 0) {
      solver->message (
          "setting decision limit to %d decisions (due to '%s')",
          decision_limit, decision_limit_specified);
      bool succeeded = solver->limit ("decisions", decision_limit);
      assert (succeeded), (void) succeeded;
    }
  }
  if (verbose () || proof_specified)
    solver->section ("proof tracing");
  if (proof_specified) {
    if (!proof_path) {
      const bool force_binary = (isatty (1) && get ("binary"));
      if (force_binary)
        set ("--no-binary");
      solver->message ("writing %s proof trace to %s'<stdout>'%s",
                       (get ("binary") ? "binary" : "non-binary"),
                       tout.green_code (), tout.normal_code ());
      if (force_binary)
        solver->message (
            "connected to terminal thus non-binary proof forced");
      solver->trace_proof (stdout, "<stdout>");
    } else if (!solver->trace_proof (proof_path))
      APPERR ("can not open and write proof trace to '%s'", proof_path);
    else
      solver->message ("writing %s proof trace to %s'%s'%s",
                       (get ("binary") ? "binary" : "non-binary"),
                       tout.green_code (), proof_path, tout.normal_code ());
  } else
    solver->verbose (1, "will not generate nor write DRAT proof");
  solver->section ("parsing input");
  dimacs_name = dimacs_path ? dimacs_path : "<stdin>";
  string help;
  if (!dimacs_path) {
    help += " ";
    help += tout.magenta_code ();
    help += "(use '-h' for a list of common options)";
    help += tout.normal_code ();
  }
  solver->message ("reading DIMACS file from %s'%s'%s%s",
                   tout.green_code (), dimacs_name, tout.normal_code (),
                   help.c_str ());
  bool incremental;
  vector<int> cube_literals;
  if (dimacs_path)
    err = solver->read_dimacs (dimacs_path, max_var, force_strict_parsing,
                               incremental, cube_literals);
  else
    err = solver->read_dimacs (stdin, dimacs_name, max_var,
                               force_strict_parsing, incremental,
                               cube_literals);
  if (err)
    APPERR ("%s", err);
  if (read_solution_path) {
    solver->section ("parsing solution");
    solver->message ("reading solution file from '%s'", read_solution_path);
    if ((err = solver->read_solution (read_solution_path)))
      APPERR ("%s", err);
  }

  solver->section ("options");
  if (optimize > 0) {
    solver->optimize (optimize);
    solver->message ();
  }
  solver->options ();

  int res = 0;

  if (incremental) {
    bool reporting = get ("report") > 1 || get ("verbose") > 0;
    if (!reporting)
      set ("report", 0);
    if (!reporting)
      solver->section ("incremental solving");
    size_t cubes = 0, solved = 0;
    size_t satisfiable = 0, unsatisfiable = 0, inconclusive = 0;
#ifndef QUIET
    bool quiet = get ("quiet");
    struct {
      double start, delta, sum;
    } time = {0, 0, 0};
#endif
    for (auto lit : cube_literals)
      if (!lit)
        cubes++;
    if (!reporting) {
      if (cubes)
        solver->message ("starting to solve %zu cubes", cubes),
            solver->message ();
      else
        solver->message ("no cube to solve");
    }
    vector<int> cube, failed;
    for (auto lit : cube_literals) {
      if (lit)
        cube.push_back (lit);
      else {
        reverse (cube.begin (), cube.end ());
        for (auto other : cube)
          solver->assume (other);
        if (solved++) {
          if (conflict_limit >= 0)
            (void) solver->limit ("conflicts", conflict_limit);
          if (decision_limit >= 0)
            (void) solver->limit ("decisions", decision_limit);
        }
#ifndef QUIET
        char buffer[256];
        if (!quiet) {
          if (reporting) {
            snprintf (buffer, sizeof buffer,
                      "solving cube %zu / %zu %.0f%%", solved, cubes,
                      percent (solved, cubes));
            solver->section (buffer);
          }
          time.start = absolute_process_time ();
        }
#endif
        res = solver->solve ();
#ifndef QUIET
        if (!quiet) {
          time.delta = absolute_process_time () - time.start;
          time.sum += time.delta;
          snprintf (buffer, sizeof buffer,
                    "%s"
                    "in %.3f sec "
                    "(%.0f%% after %.2f sec at %.0f ms/cube)"
                    "%s",
                    tout.magenta_code (), time.delta,
                    percent (solved, cubes), time.sum,
                    relative (1e3 * time.sum, solved), tout.normal_code ());
          if (reporting)
            solver->message ();
          const char *cube_str, *status_str, *color_code;
          if (res == 10) {
            cube_str = "CUBE";
            color_code = tout.green_code ();
            status_str = "SATISFIABLE";
          } else if (res == 20) {
            cube_str = "CUBE";
            color_code = tout.cyan_code ();
            status_str = "UNSATISFIABLE";
          } else {
            cube_str = "cube";
            color_code = tout.magenta_code ();
            status_str = "inconclusive";
          }
          const char *fmt;
          if (reporting)
            fmt = "%s%s %zu %s%s %s";
          else
            fmt = "%s%s %zu %-13s%s %s";
          solver->message (fmt, color_code, cube_str, solved, status_str,
                           tout.normal_code (), buffer);
        }
#endif
        if (res == 10) {
          satisfiable++;
          solver->conclude ();
          break;
        } else if (res == 20) {
          unsatisfiable++;
          solver->conclude ();
          for (auto other : cube)
            if (solver->failed (other))
              failed.push_back (other);
          for (auto other : failed)
            solver->add (-other);
          solver->add (0);
          failed.clear ();
        } else {
          assert (!res);
          inconclusive++;
          if (timesup)
            break;
        }
        cube.clear ();
      }
    }
    solver->section ("incremental summary");
    solver->message ("%zu cubes solved %.0f%%", solved,
                     percent (solved, cubes));
    solver->message ("%zu cubes inconclusive %.0f%%", inconclusive,
                     percent (inconclusive, solved));
    solver->message ("%zu cubes unsatisfiable %.0f%%", unsatisfiable,
                     percent (unsatisfiable, solved));
    solver->message ("%zu cubes satisfiable %.0f%%", satisfiable,
                     percent (satisfiable, solved));

    if (inconclusive && res == 20)
      res = 0;
  } else {
    solver->section ("solving");
    res = solver->solve ();
  }

  if (proof_specified) {
    solver->section ("closing proof");
    solver->close_proof_trace (!get ("quiet"));
  }

  if (output_path) {
    solver->section ("writing output");
    solver->message ("writing simplified CNF to DIMACS file %s'%s'%s",
                     tout.green_code (), output_path, tout.normal_code ());
    err = solver->write_dimacs (output_path, max_var);
    if (err)
      APPERR ("%s", err);
  }

  if (extension_path) {
    solver->section ("writing extension");
    solver->message ("writing extension stack to %s'%s'%s",
                     tout.green_code (), extension_path,
                     tout.normal_code ());
    err = solver->write_extension (extension_path);
    if (err)
      APPERR ("%s", err);
  }

  solver->section ("result");

  FILE *write_result_file;
  write_result_file = stdout;
  if (write_result_path) {
    write_result_file = fopen (write_result_path, "w");
    if (!write_result_file)
      APPERR ("could not write solution to '%s'", write_result_path);
    solver->message ("writing result to '%s'", write_result_path);
  }

  if (res == 10) {
    if (status)
      fputs ("s SATISFIABLE\n", write_result_file);
    if (witness)
      print_witness (write_result_file);
  } else if (res == 20 && status)
    fputs ("s UNSATISFIABLE\n", write_result_file);
  else if (status)
    fputs ("c UNKNOWN\n", write_result_file);
  fflush (write_result_file);
  if (write_result_path)
    fclose (write_result_file);
  solver->statistics ();
  solver->resources ();
  solver->section ("shutting down");
  solver->message ("exit %d", res);
  if (!res && timesup)
    fputs ("c Timeout reached! 😅 This instance is a real thinker.\n"
           "c 🚧 🚧 🚧 Please consider contributing it to the page\n"
           "c https://mysolvertimesout.org/#sat in order to improve\n"
           "c automated reasoning. 🚧 🚧 🚧\n",
           write_result_file);
  if (less_pipe) {
    close (1);
    pclose (less_pipe);
  }
#ifndef _WIN32
  if (time_limit > 0)
    alarm (0);
#endif

  return res;
}

/*------------------------------------------------------------------------*/

// The real initialization is delayed.

void App::init () {

  assert (!solver);

#ifndef _WIN32
  time_limit = -1;
#endif
  force_strict_parsing = 1;
  force_writing = false;
  max_var = 0;
  timesup = false;

  // Call 'new Solver' only after setting 'reportdefault' and do not
  // add this call to the member initialization above. This is because for
  // stand-alone usage the default report default value is 'true' while for
  // library usage it should remain 'false'.  See the explanation in
  // 'options.hpp' related to 'reportdefault' for details.

  CaDiCaL::Options::reportdefault = 1;
  solver = new Solver ();
  Signal::set (this);
}

/*------------------------------------------------------------------------*/

App::App () : solver (0) {} // Only partially initialize the app.

App::~App () {
  if (!solver)
    return; // Only partially initialized.
  Signal::reset ();
  delete solver;
}

/*------------------------------------------------------------------------*/

#ifndef QUIET

void App::signal_message (const char *msg, int sig) {
  solver->message ("%s%s %ssignal %d%s (%s)%s", tout.red_code (), msg,
                   tout.bright_red_code (), sig, tout.red_code (),
                   Signal::name (sig), tout.normal_code ());
}

#endif

void App::catch_signal (int sig) {
#ifndef QUIET
  if (!get ("quiet")) {
    solver->message ();
    signal_message ("caught", sig);
    solver->section ("result");
    solver->message ("UNKNOWN");
    solver->statistics ();
    solver->resources ();
    solver->message ();
    signal_message ("raising", sig);
  }
#else
  (void) sig;
#endif
}

void App::catch_alarm () {
  // Both approaches work. We keep them here for illustration purposes.
#if 0 // THIS IS AN ALTERNATIVE WE WANT TO KEEP AROUND.
  solver->terminate (); // Immediate asynchronous call into solver.
#else
  timesup = true; // Wait for solver to call 'App::terminate ()'.
#endif
}

void Solver::decide_first (int lit) {
  REQUIRE_VALID_LIT (lit);
  int idx = lit > 0 ? lit : -lit;
  internal->priority_decisions.push_back (idx);
}

void Solver::bump (int lit) {
  REQUIRE_VALID_LIT (lit);
  internal->bump_variable (lit);
}

} // namespace CaDiCaL
