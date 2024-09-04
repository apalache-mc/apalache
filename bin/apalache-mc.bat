@echo off
rem Run the APALACHE model checker
rem
rem NOTE: The primary intended use for this script is to be copied into the
rem packaged produced.
rem
rem Gabriela Moreira, 2024

rem Set the directory where the script is run from
set "DIR=%~dp0"

rem Set the path to the APALACHE JAR file
set "APALACHE_JAR=%DIR%\..\lib\apalache.jar"

rem Set JVM arguments
set "JVM_ARGS="

rem Check if the APALACHE JAR file exists
if not exist "%APALACHE_JAR%" (
    echo ERROR: No file found at %APALACHE_JAR%
    echo Ensure you have run 'make package' and are running the script from the
    echo distribution package, or else set APALACHE_JAR to point to your custom
    echo build jar.
    exit /b 1
)

rem Check if the heap size is already set
echo %JVM_ARGS% | findstr /C:"-Xmx" >nul || echo %JVM_ARGS% | findstr /C:"-XX:MaxRAMPercentage" >nul || set "JVM_ARGS=-Xmx4096m"

rem Check whether the command-line arguments contain the debug flag
echo %* | find "--debug" >nul && (
    echo # Tool home: %DIR%
    echo # Package:   %APALACHE_JAR%
    echo # JVM args: %JVM_ARGS%
    echo #
)

rem Run the Java command
java %JVM_ARGS% -jar "%APALACHE_JAR%" %*
