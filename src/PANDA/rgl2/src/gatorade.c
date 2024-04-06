/*********************************************************************
* Software License Agreement (BSD License)
*
*  Copyright (c) 2011, Rice University.
*  All rights reserved.
*
*  Redistribution and use in source and binary forms, with or without
*  modification, are permitted provided that the following conditions
*  are met:
*
*   * Redistributions of source code must retain the above copyright
*     notice, this list of conditions and the following disclaimer.
*   * Redistributions in binary form must reproduce the above
*     copyright notice, this list of conditions and the following
*     disclaimer in the documentation and/or other materials provided
*     with the distribution.
*   * Neither the name of the Rice University nor the names of its
*     contributors may be used to endorse or promote products derived
*     from this software without specific prior written permission.
*
*  THIS SOFTWARE IS PROVIDED BY THE COPYRIGHT HOLDERS AND CONTRIBUTORS
*  "AS IS" AND ANY EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT
*  LIMITED TO, THE IMPLIED WARRANTIES OF MERCHANTABILITY AND FITNESS
*  FOR A PARTICULAR PURPOSE ARE DISCLAIMED. IN NO EVENT SHALL THE
*  COPYRIGHT OWNER OR CONTRIBUTORS BE LIABLE FOR ANY DIRECT, INDIRECT,
*  INCIDENTAL, SPECIAL, EXEMPLARY, OR CONSEQUENTIAL DAMAGES (INCLUDING,
*  BUT NOT LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS OR SERVICES;
*  LOSS OF USE, DATA, OR PROFITS; OR BUSINESS INTERRUPTION) HOWEVER
*  CAUSED AND ON ANY THEORY OF LIABILITY, WHETHER IN CONTRACT, STRICT
*  LIABILITY, OR TORT (INCLUDING NEGLIGENCE OR OTHERWISE) ARISING IN
*  ANY WAY OUT OF THE USE OF THIS SOFTWARE, EVEN IF ADVISED OF THE
*  POSSIBILITY OF SUCH DAMAGE.
*********************************************************************/

/* Author: Andrew Ladd */


#include "gatorade.h"


unsigned int dprint_threshold;

/**
 * This is where the fun begins. The main parses the command line
 * parameters and dispatches the task to the appropriate handler. See
 * spin_module and wring_module for more details.
 */
int main(int argc, char** argv) {
  printf("This is the translator for non-deterministic Buechi automata!\n");
  if (argc == 1) {
    print_usage(argv[0]);
    exit(54337);
  }
  
  params_t params = parse_params(argc, argv);
  
  if (params->rank == 0) {
    print_params(1, stdout, params);
  }

  
  if (params->singleFileMode) {
    // Figure out the source directory
    int c = strlen(params->singleFileName);
    while (c > 0 &&
	   params->singleFileName[c] != '/') {
      c--;
    }

    if (c==0) {
      fprintf(stderr, "Couldn't parse the directory of file %s\n", params->singleFileName);
      exit(1);
    }
    
    (params->singleFileName)[c] = '\0';
    params->src = params->singleFileName;
    params->dest = params->tmp;
    dprint(3, "The source directory is %s\n", params->src);
    dprint(3, "The file name is %s\n", (params->singleFileName + c + 1));
    
    if (params->workmode == WRING)
      processSingleFile(params->singleFileName + c + 1, params);

    else if (params->workmode == FINITESPIN)
      finite_spin_single_file(params->singleFileName + c + 1, params);
    
    else if (params->workmode == SPIN)
      infinite_spin_single_file(params->singleFileName + c + 1, params);

    else if ((params->workmode == CADENCE) || (params->workmode == NUSMV))
      smv_process_single_file(params->singleFileName + c + 1, params);

    else
      unix_error("Unknown working mode: %s\n", wrkmd2str(params->workmode));
    exit(0);    
  }




  /** There must be a source directory! */
  if(! directory_exists(params->src))
    unix_error("Source directory not found!");
  
  else
    dprint(7, "Source directory found.\n");
  
  /** If the destination directory doesn't exist, create it */
  if (! directory_exists(params->dest)) {
    if (params->rank == 0)
      Mkdir(params->dest, STANDARD_PERMISSIONS);
    else
      while (! directory_exists(params->dest)) {
	sleep(1);
      }
  }

  /** If the temporary directory doesn't exist, create it */
  if (! directory_exists(params->tmp)) {
    if (params->rank == 0)
      Mkdir(params->tmp, STANDARD_PERMISSIONS);
    else
      while (! directory_exists(params->tmp)) {
	sleep(1);
      }
  }


  dprint(7, "Destination directory OK\n");
  
  print_params_to_log_file(params);

  
  /** Simple error checking */
  if (params->rank >= params->procs)
    unix_error("Rank number exceeds number of processors");
  
  if (0==strcmp(params->src, params->dest))
    unix_warning("Source and destination directories are the same!");
 
  
  dprint(7, "Passed the minor error checks!\n");
  /** Read all applicable files from the source directory */
  dirent_t* a_selected_files;

  fs_params = Malloc(sizeof(struct fileselector_params));
  fs_params->procs = params->procs;
  fs_params->rank  = params->rank;

  dprint(8, "Set the fileselector parameters.\n");
  int n_files = Scandir(params->src, &a_selected_files, file_selector, alphasort);
  
  dprint(7, "Found %d files\n", n_files);
  
  for (uint_t i=0; i<n_files; i++) {
    
    if (params->workmode == WRING)
      processSingleFile(a_selected_files[i]->d_name, params);

    else if (params->workmode == SPIN)
      infinite_spin_single_file(a_selected_files[i]->d_name, params);
    
    else if (params->workmode == CADENCE || params->workmode == NUSMV)
      smv_process_single_file(a_selected_files[i]->d_name, params);
    else
      unix_error("Undefined workmode %s", wrkmd2str(params->workmode));
  }

  
  free(a_selected_files);
  exit(0);
  
  dprint(2, "Done.\n");
  exit(0);
}
