# LTLL - LTL Learning from Positive Examples via Model Counting

Clone this repository and **initialize all submodules** by running 

```shell
git clone git@projects.cispa.saarland:c01rabe/ltl-learning.git
cd ltl-learning
git submodule init
git submodule update
cd tool
```

When pulling a new version, make sure to update the submodules by re-running `git submodule update`.

## Structure 

- `src/` contains the source code of LTL
- `examples/` contains various examples files
- `app/` is the target folder for the build. The final LTLL executable will be placed here. 

## Build LTLL

### Dependencies

We require the following dependencies:

- [.NET 7 SDK](https://dotnet.microsoft.com/en-us/download) (tested with version 7.0.306)
- [spot](https://spot.lrde.epita.fr/) (tested with version 2.11.5)

Install the .NET 7 SDK (see [here](https://dotnet.microsoft.com/en-us/download) for details) and make sure it is installed correctly by running `dotnet --version`.
Download and build spot (details can be found [here](https://spot.lrde.epita.fr/)). 
You can place the spot executables in any location of your choosing. 

### Build LTLL

To build LTLL run the following (when in the main directory of this repository).

```shell
cd src/ltll
dotnet build -c "release" -o ../../app
cd ../..
```

Afterward, the LTLL executable (called `ltll`) is located in the `app/` folder.
The LTLL executable is not standalone and requires the other files located in the `app/` folder (as is usual for .NET applications).
Moreover, it will only run on systems that have the .NET Core Runtime installed. 


### Connect spot to AutoHyper

LTLL requires the *autfilt*, *ltl2tgba*, and *randltl* tools from the [spot](https://spot.lrde.epita.fr/) library.
LTLL is designed such that it only needs the *absolute* path to these executables, so they can be installed and placed at whatever locations fits best.
The absolute paths are specified in a `paths.json` configuration file. 
This file must be located in the same directory as the AutoHyper executable (this convention makes it easy to find the config file, independent of the relative path AutoHyper is called from). 
We already provide a template file `app/paths.json` that **needs to be modified**. 
After having built spot, paste the absolute path to the *autfilt*, *ltl2tgba*, and *randltl* executables to the `paths.json` file. 
For example, if `/usr/bin/autfilt`, `/usr/bin/ltl2tgba`, `/usr/bin/randltl` are the *autfilt*, *ltl2tgba*, and *randltl* executables, respectively, the content of `app/paths.json` should be

```json
{
    "autfilt":"/usr/bin/autfilt",
    "ltl2tgba":"/usr/bin/ltl2tgba",
    "randltl":"/usr/bin/randltl"
}
```

### Run LTLL

To test that the paths have been setup correctly, we can verify our first instance by running

```shell
app/ltll ./examples/traces_ga.txt
```

