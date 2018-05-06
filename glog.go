// Go support for leveled logs, analogous to https://code.google.com/p/google-glog/
//
// Copyright 2013 Google Inc. All Rights Reserved.
//
// Licensed under the Apache License, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// You may obtain a copy of the License at
//
//     http://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software
// distributed under the License is distributed on an "AS IS" BASIS,
// WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
// See the License for the specific language governing permissions and
// limitations under the License.

// Package glog implements logging similar to the Google-internal C++
// INFO/ERROR/V setup.  It provides functions Info, Warning, Error, Fatal, plus
// formatting variants such as Infof. It also provides V-style logging,
// controlled by a logger's verbosity.
//
// This is a fork of the github.com/golang/glog package to remove global state
// (and specifically flagset dependency) from glog.
//
// Basic examples:
//
//      log := glog.NewLogger(glog.NewOptions())
//
//      log.Info("Prepare to repel boarders")
//
//      log.Fatalf("Initialization failed: %s", err)
//
// See the documentation for the V function for an explanation of these examples:
//
//      if log.V(2) != nil {
//              log.Info("Starting transaction...")
//      }
//
//      log.V(2).Infoln("Processed", nItems, "elements")
//
// Log output is buffered and written periodically using Flush.
// Programs should call Flush, or Close, before exiting to guarantee all log
// output is written.
//
// By default, all log statements write to files in a temporary directory.
// This behavior can be modified by initializing a logger with a custom Options
// struct, such as by setting either ToStderr or AlsoToStderr to true.
//
package glog

import (
	"bufio"
	"bytes"
	"errors"
	"fmt"
	"io"
	stdLog "log"
	"os"
	"path/filepath"
	"runtime"
	"strconv"
	"strings"
	"sync"
	"sync/atomic"
	"time"
)

// Severity identifies the sort of log: info, warning etc. It also implements
// the flag.Value interface.
type Severity int32 // sync/atomic int32

// These constants identify the log levels in order of increasing severity.
// A message written to a high-severity log file is also written to each
// lower-severity log file.
const (
	LevelInfo Severity = iota
	LevelWarning
	LevelError
	LevelFatal
	numSeverity = 4
)

const severityChar = "IWEF"

var severityName = []string{
	LevelInfo:    "INFO",
	LevelWarning: "WARNING",
	LevelError:   "ERROR",
	LevelFatal:   "FATAL",
}

// get returns the value of the severity.
func (s *Severity) get() Severity {
	return Severity(atomic.LoadInt32((*int32)(s)))
}

// set sets the value of the severity.
func (s *Severity) set(val Severity) {
	atomic.StoreInt32((*int32)(s), int32(val))
}

func severityByName(s string) (Severity, bool) {
	s = strings.ToUpper(s)
	for i, name := range severityName {
		if name == s {
			return Severity(i), true
		}
	}
	return 0, false
}

// OutputStats tracks the number of output lines and bytes written.
type OutputStats struct {
	lines int64
	bytes int64
}

// Lines returns the number of lines written.
func (s *OutputStats) Lines() int64 {
	return atomic.LoadInt64(&s.lines)
}

// Bytes returns the number of bytes written.
func (s *OutputStats) Bytes() int64 {
	return atomic.LoadInt64(&s.bytes)
}

// Level is exported because it appears in the arguments to V and is
// the type of the Verbosity option, which can be set programmatically.
// It's a distinct type because we want to discriminate it from Severity.

// Level is treated as a sync/atomic int32.

// Level specifies a level of verbosity for V logs. *Level implements
// flag.Value. A logger's Level can be set using SetVerbosity.
type Level int32

// get returns the value of the Level.
func (l *Level) get() Level {
	return Level(atomic.LoadInt32((*int32)(l)))
}

// set sets the value of the Level.
func (l *Level) set(val Level) {
	atomic.StoreInt32((*int32)(l), int32(val))
}

// String is part of the flag.Value interface.
func (l *Level) String() string {
	return strconv.FormatInt(int64(*l), 10)
}

// Get is part of the flag.Value interface.
func (l *Level) Get() interface{} {
	return *l
}

// Set is part of the flag.Value interface.
func (l *Level) Set(value string) error {
	v, err := strconv.Atoi(value)
	if err != nil {
		return err
	}
	*l = Level(v)
	return nil
}

// moduleSpec represents the setting of the -vmodule flag.
type moduleSpec struct {
	filter []modulePat
}

// modulePat contains a filter for the -vmodule flag.
// It holds a verbosity level and a file pattern to match.
type modulePat struct {
	pattern string
	literal bool // The pattern is a literal string
	level   Level
}

// match reports whether the file matches the pattern. It uses a string
// comparison if the pattern contains no metacharacters.
func (m *modulePat) match(file string) bool {
	if m.literal {
		return file == m.pattern
	}
	match, _ := filepath.Match(m.pattern, file)
	return match
}

var errVmoduleSyntax = errors.New("syntax error: expect comma-separated list of filename=N")

// Syntax: -vmodule=recordio=2,file=1,gfs*=3
func (m *moduleSpec) Set(value string) error {
	var filter []modulePat
	for _, pat := range strings.Split(value, ",") {
		if len(pat) == 0 {
			// Empty strings such as from a trailing comma can be ignored.
			continue
		}
		patLev := strings.Split(pat, "=")
		if len(patLev) != 2 || len(patLev[0]) == 0 || len(patLev[1]) == 0 {
			return errVmoduleSyntax
		}
		pattern := patLev[0]
		v, err := strconv.Atoi(patLev[1])
		if err != nil {
			return errors.New("syntax error: expect comma-separated list of filename=N")
		}
		if v < 0 {
			return errors.New("negative value for vmodule level")
		}
		if v == 0 {
			continue // Ignore. It's harmless but no point in paying the overhead.
		}
		// TODO: check syntax of filter?
		filter = append(filter, modulePat{pattern, isLiteral(pattern), Level(v)})
	}
	m.filter = filter
	return nil
}

// isLiteral reports whether the pattern is a literal string, that is, has no metacharacters
// that require filepath.Match to be called to match the pattern.
func isLiteral(pattern string) bool {
	return !strings.ContainsAny(pattern, `\*?[]`)
}

// traceLocation represents the setting of the -log_backtrace_at flag.
type traceLocation struct {
	file string
	line int
}

// isSet reports whether the trace location has been specified.
// logging.mu is held.
func (t *traceLocation) isSet() bool {
	return t.line > 0
}

// match reports whether the specified file and line matches the trace location.
// The argument file name is the full path, not the basename specified in the flag.
// logging.mu is held.
func (t *traceLocation) match(file string, line int) bool {
	if t.line != line {
		return false
	}
	if i := strings.LastIndex(file, "/"); i >= 0 {
		file = file[i+1:]
	}
	return t.file == file
}

var errTraceSyntax = errors.New("syntax error: expect file.go:234")

// Syntax: -log_backtrace_at=gopherflakes.go:234
// Note that unlike vmodule the file extension is included here.
func (t *traceLocation) Set(value string) error {
	if value == "" {
		// Unset.
		t.line = 0
		t.file = ""
		return nil
	}
	fields := strings.Split(value, ":")
	if len(fields) != 2 {
		return errTraceSyntax
	}
	file, line := fields[0], fields[1]
	if !strings.Contains(file, ".") {
		return errTraceSyntax
	}
	v, err := strconv.Atoi(line)
	if err != nil {
		return errTraceSyntax
	}
	if v <= 0 {
		return errors.New("negative or zero value for level")
	}

	t.line = v
	t.file = file

	return nil
}

// flushSyncWriter is the interface satisfied by logging destinations.
type flushSyncWriter interface {
	Flush() error
	Sync() error
	io.Writer
}

// Flush flushes all pending log I/O.
func (l *Logger) Flush() {
	l.lockAndFlushAll()
}

// Close flushes all pending I/O and stops the flush background goroutine.
func (l *Logger) Close() {
	l.Flush()
	close(l.stop)
	<-l.stopped
}

// Options controls a Logger's behavior at initialization.
type Options struct {
	// LogName is the name of the log file to write to.
	// This option has no effect if ToStderr is true.
	LogName string

	// ToStderr sets whether to log to standard error instead of files.
	// ToStderr takes precedence over AlsoToStderr.
	ToStderr bool
	// AlsoToStderr sets whether to log to standard error as well as to files.
	// ToStderr takes precedence over AlsoToStderr.
	AlsoToStderr bool

	// StderrThreshold sets the minimum severity a log message needs to be to write it to
	// standard error, regardless of whether ToStderr or AlsoToStderr is true.
	StderrThreshold Severity
	// PrintLevel controls the severity of log messages written using Logger.Print, .Printf,
	// .Println, and .PrintDepth.
	PrintLevel Severity
	// Verbosity is an integer indicating the desired verbosity of logs.
	// The meaning of different levels is programmer-defined and is only used to determine if
	// the verbosity (see the Logger.V method) is at least the requested level to print
	// a message.
	Verbosity Level

	// VModule sets the verbosity of different files.
	//
	// The syntax of the option is a comma-separated list of pattern=N, where pattern is
	// a literal file name (minus the ".go" suffix) or "glob" pattern and N is a V level.
	//
	// For instance, a VModule of "gopher*=3" sets the V level to 3 in all Go files whose names
	// begin "gopher".
	VModule string
	// TraceLocation specifies a file and line number to print a trace on alongside a log
	// message occurring on that line.
	//
	// The expected format is "file:line". For example, "main.go:62" to print a backtrace when
	// a Logger prints from line 62 of main.go.
	TraceLocation string
}

// NewOptions returns a basic set of Options for creating a logger.
// By default, the log name is set to the progam name, and both the standard error threshold and
// Print level is set to LevelError.
func NewOptions() Options {
	return Options{
		LogName:         filepath.Base(os.Args[0]),
		StderrThreshold: LevelError,
		PrintLevel:      LevelError,
	}
}

// Logger writes formatted log messages to files and/or standard error.
type Logger struct {
	// Previously known as loggingT. Most previously-global data (e.g., Stats) has been migrated
	// into this struct.

	// Name of the log program or log, used when creating log files.
	logname string

	// Boolean flags. Not handled atomically because the flag.Value interface
	// does not let us avoid the =true, and that shorthand is necessary for
	// compatibility. TODO: does this matter enough to fix? Seems unlikely.
	toStderr     bool // The -logtostderr flag.
	alsoToStderr bool // The -alsologtostderr flag.

	// Level flag. Handled atomically.
	stderrThreshold Severity // The -stderrthreshold flag.
	printLevel      Severity // The level to write Print* logs at.

	// freeList is a list of byte buffers, maintained under freeListMu.
	freeList *buffer
	// freeListMu maintains the free list. It is separate from the main mutex
	// so buffers can be grabbed and printed to without holding the main lock,
	// for better parallelization.
	freeListMu sync.Mutex

	// mu protects the remaining elements of this structure and is
	// used to synchronize logging.
	mu sync.Mutex
	// file holds writer for each of the log types.
	file [numSeverity]flushSyncWriter
	// pcs is used in V to avoid an allocation when computing the caller's PC.
	pcs [1]uintptr
	// vmap is a cache of the V Level for each V() call site, identified by PC.
	// It is wiped whenever the vmodule flag changes state.
	vmap map[uintptr]Level
	// filterLength stores the length of the vmodule filter chain. If greater
	// than zero, it means vmodule is enabled. It may be read safely
	// using sync.LoadInt32, but is only modified under mu.
	filterLength int32
	// traceLocation is the state of the -log_backtrace_at flag.
	traceLocation traceLocation
	// These flags are modified only under lock, although verbosity may be fetched
	// safely using atomic.LoadInt32.
	vmodule   moduleSpec // The state of the -vmodule flag.
	verbosity Level      // V logging level, the value of the -v flag/

	stop    chan struct{}
	stopped chan struct{}

	severityStats [numSeverity]*OutputStats
	// Stats tracks the number of lines of output and number of bytes
	// per severity level. Values must be read with atomic.LoadInt64.
	Stats struct {
		Info, Warning, Error OutputStats
	}
}

var errLogNameEmpty = errors.New("glog: log name may not be empty when writing to files")

// NewLog initializes and returns a new *Logger. If initialization fails, nil and an error are
// returned.
func NewLog(opts Options) (*Logger, error) {
	if opts.LogName == "" && !opts.ToStderr {
		return nil, errLogNameEmpty
	}

	switch opts.StderrThreshold {
	case LevelInfo, LevelWarning, LevelError, LevelFatal:
	default:
		return nil, fmt.Errorf("invalid stderr severity: %d", int32(opts.StderrThreshold))
	}

	L := &Logger{
		toStderr:        opts.ToStderr,
		alsoToStderr:    opts.AlsoToStderr,
		stderrThreshold: opts.StderrThreshold,
		printLevel:      opts.PrintLevel,
		stop:            make(chan struct{}),
		stopped:         make(chan struct{}),
	}

	if err := L.SetPrintLevel(opts.PrintLevel); err != nil {
		return nil, err
	}

	L.severityStats = [numSeverity]*OutputStats{
		&L.Stats.Info,
		&L.Stats.Warning,
		&L.Stats.Error,
	}

	if err := L.vmodule.Set(opts.VModule); err != nil {
		return nil, err
	}

	if err := L.traceLocation.Set(opts.TraceLocation); err != nil {
		return nil, err
	}

	L.setVState(L.verbosity, L.vmodule.filter, false)

	go L.flushDaemon()

	return L, nil
}

// SetPrintLevel sets the logging severity of Print, Println, Printf, and PrintDepth.
// This can be useful for passing a Logger to an interface expecting only a Print-like method set.
func (l *Logger) SetPrintLevel(sev Severity) error {
	switch sev {
	case LevelInfo, LevelWarning, LevelError, LevelFatal:
		l.printLevel.set(sev)
		return nil
	}
	return fmt.Errorf("invalid severity: %d", int32(sev))
}

//SetVerbosity sets the verbosity (V) of the Logger.
func (l *Logger) SetVerbosity(v Level) {
	l.mu.Lock()
	defer l.mu.Unlock()
	l.setVState(v, l.vmodule.filter, len(l.vmodule.filter) > 0)
}

// SetVModule sets the vmodule of the Logger.
func (l *Logger) SetVModule(vmodule string) error {
	var vm moduleSpec
	if err := vm.Set(vmodule); err != nil {
		return err
	}
	l.mu.Lock()
	defer l.mu.Unlock()
	l.setVState(l.verbosity, vm.filter, len(vm.filter) > 0)
	return nil
}

// SetTraceLocation sets the trace location of the Logger.
func (l *Logger) SetTraceLocation(loc string) error {
	var tl traceLocation
	if err := tl.Set(loc); err != nil {
		return err
	}
	l.mu.Lock()
	defer l.mu.Unlock()
	l.traceLocation = tl
	return nil
}

// buffer holds a byte Buffer for reuse. The zero value is ready for use.
type buffer struct {
	bytes.Buffer
	tmp  [64]byte // temporary byte array for creating headers.
	next *buffer
}

// setVState sets a consistent state for V logging.
// l.mu is held.
func (l *Logger) setVState(verbosity Level, filter []modulePat, setFilter bool) {
	// Turn verbosity off so V will not fire while we are in transition.
	l.verbosity.set(0)
	// Ditto for filter length.
	atomic.StoreInt32(&l.filterLength, 0)

	// Set the new filters and wipe the pc->Level map if the filter has changed.
	if setFilter {
		l.vmodule.filter = filter
		l.vmap = make(map[uintptr]Level)
	}

	// Things are consistent now, so enable filtering and verbosity.
	// They are enabled in order opposite to that in V.
	atomic.StoreInt32(&l.filterLength, int32(len(filter)))
	l.verbosity.set(verbosity)
}

// getBuffer returns a new, ready-to-use buffer.
func (l *Logger) getBuffer() *buffer {
	l.freeListMu.Lock()
	b := l.freeList
	if b != nil {
		l.freeList = b.next
	}
	l.freeListMu.Unlock()
	if b == nil {
		b = new(buffer)
	} else {
		b.next = nil
		b.Reset()
	}
	return b
}

// putBuffer returns a buffer to the free list.
func (l *Logger) putBuffer(b *buffer) {
	if b.Len() >= 256 {
		// Let big buffers die a natural death.
		return
	}
	l.freeListMu.Lock()
	b.next = l.freeList
	l.freeList = b
	l.freeListMu.Unlock()
}

var timeNow = time.Now // Stubbed out for testing.

/*
header formats a log header as defined by the C++ implementation.
It returns a buffer containing the formatted header and the user's file and line number.
The depth specifies how many stack frames above lives the source line to be identified in the log message.

Log lines have this form:
	Lmmdd hh:mm:ss.uuuuuu threadid file:line] msg...
where the fields are defined as follows:
	L                A single character, representing the log level (eg 'I' for INFO)
	mm               The month (zero padded; ie May is '05')
	dd               The day (zero padded)
	hh:mm:ss.uuuuuu  Time in hours, minutes and fractional seconds
	threadid         The space-padded thread ID as returned by GetTID()
	file             The file name
	line             The line number
	msg              The user-supplied message
*/
func (l *Logger) header(s Severity, depth int) (*buffer, string, int) {
	_, file, line, ok := runtime.Caller(3 + depth)
	if !ok {
		file = "???"
		line = 1
	} else {
		slash := strings.LastIndex(file, "/")
		if slash >= 0 {
			file = file[slash+1:]
		}
	}
	return l.formatHeader(s, file, line), file, line
}

// formatHeader formats a log header using the provided file name and line number.
func (l *Logger) formatHeader(s Severity, file string, line int) *buffer {
	now := timeNow()
	if line < 0 {
		line = 0 // not a real line number, but acceptable to someDigits
	}
	if s > LevelFatal {
		s = LevelInfo // for safety.
	}
	buf := l.getBuffer()

	// Avoid Fprintf, for speed. The format is so simple that we can do it quickly by hand.
	// It's worth about 3X. Fprintf is hard.
	_, month, day := now.Date()
	hour, minute, second := now.Clock()
	// Lmmdd hh:mm:ss.uuuuuu threadid file:line]
	buf.tmp[0] = severityChar[s]
	buf.twoDigits(1, int(month))
	buf.twoDigits(3, day)
	buf.tmp[5] = ' '
	buf.twoDigits(6, hour)
	buf.tmp[8] = ':'
	buf.twoDigits(9, minute)
	buf.tmp[11] = ':'
	buf.twoDigits(12, second)
	buf.tmp[14] = '.'
	buf.nDigits(6, 15, now.Nanosecond()/1000, '0')
	buf.tmp[21] = ' '
	buf.nDigits(7, 22, pid, ' ') // TODO: should be TID
	buf.tmp[29] = ' '
	buf.Write(buf.tmp[:30])
	buf.WriteString(file)
	buf.tmp[0] = ':'
	n := buf.someDigits(1, line)
	buf.tmp[n+1] = ']'
	buf.tmp[n+2] = ' '
	buf.Write(buf.tmp[:n+3])
	return buf
}

// Some custom tiny helper functions to print the log header efficiently.

const digits = "0123456789"

// twoDigits formats a zero-prefixed two-digit integer at buf.tmp[i].
func (buf *buffer) twoDigits(i, d int) {
	buf.tmp[i+1] = digits[d%10]
	d /= 10
	buf.tmp[i] = digits[d%10]
}

// nDigits formats an n-digit integer at buf.tmp[i],
// padding with pad on the left.
// It assumes d >= 0.
func (buf *buffer) nDigits(n, i, d int, pad byte) {
	j := n - 1
	for ; j >= 0 && d > 0; j-- {
		buf.tmp[i+j] = digits[d%10]
		d /= 10
	}
	for ; j >= 0; j-- {
		buf.tmp[i+j] = pad
	}
}

// someDigits formats a zero-prefixed variable-width integer at buf.tmp[i].
func (buf *buffer) someDigits(i, d int) int {
	// Print into the top, then copy down. We know there's space for at least
	// a 10-digit number.
	j := len(buf.tmp)
	for {
		j--
		buf.tmp[j] = digits[d%10]
		d /= 10
		if d == 0 {
			break
		}
	}
	return copy(buf.tmp[i:], buf.tmp[j:])
}

func (l *Logger) println(s Severity, args ...interface{}) {
	buf, file, line := l.header(s, 0)
	fmt.Fprintln(buf, args...)
	l.output(s, buf, file, line, false)
}

func (l *Logger) print(s Severity, args ...interface{}) {
	l.printDepth(s, 1, args...)
}

func (l *Logger) printDepth(s Severity, depth int, args ...interface{}) {
	buf, file, line := l.header(s, depth)
	fmt.Fprint(buf, args...)
	if buf.Bytes()[buf.Len()-1] != '\n' {
		buf.WriteByte('\n')
	}
	l.output(s, buf, file, line, false)
}

func (l *Logger) printf(s Severity, format string, args ...interface{}) {
	buf, file, line := l.header(s, 0)
	fmt.Fprintf(buf, format, args...)
	if buf.Bytes()[buf.Len()-1] != '\n' {
		buf.WriteByte('\n')
	}
	l.output(s, buf, file, line, false)
}

// printWithFileLine behaves like print but uses the provided file and line number.  If
// alsoLogToStderr is true, the log message always appears on standard error; it
// will also appear in the log file unless --logtostderr is set.
func (l *Logger) printWithFileLine(s Severity, file string, line int, alsoToStderr bool, args ...interface{}) {
	buf := l.formatHeader(s, file, line)
	fmt.Fprint(buf, args...)
	if buf.Bytes()[buf.Len()-1] != '\n' {
		buf.WriteByte('\n')
	}
	l.output(s, buf, file, line, alsoToStderr)
}

// output writes the data to the log files and releases the buffer.
func (l *Logger) output(s Severity, buf *buffer, file string, line int, alsoToStderr bool) {
	l.mu.Lock()
	if l.traceLocation.isSet() {
		if l.traceLocation.match(file, line) {
			buf.Write(stacks(false))
		}
	}
	data := buf.Bytes()
	if l.toStderr {
		os.Stderr.Write(data)
	} else {
		if alsoToStderr || l.alsoToStderr || s >= l.stderrThreshold.get() {
			os.Stderr.Write(data)
		}
		if l.file[s] == nil {
			if err := l.createFiles(s); err != nil {
				os.Stderr.Write(data) // Make sure the message appears somewhere.
				l.exit(err)
			}
		}
		switch s {
		case LevelFatal:
			l.file[LevelFatal].Write(data)
			fallthrough
		case LevelError:
			l.file[LevelError].Write(data)
			fallthrough
		case LevelWarning:
			l.file[LevelWarning].Write(data)
			fallthrough
		case LevelInfo:
			l.file[LevelInfo].Write(data)
		}
	}
	if s == LevelFatal {
		// If we got here via Exit rather than Fatal, print no stacks.
		if atomic.LoadUint32(&fatalNoStacks) > 0 {
			l.mu.Unlock()
			l.timeoutFlush(10 * time.Second)
			os.Exit(1)
		}
		// Dump all goroutine stacks before exiting.
		// First, make sure we see the trace for the current goroutine on standard error.
		// If -logtostderr has been specified, the loop below will do that anyway
		// as the first stack in the full dump.
		if !l.toStderr {
			os.Stderr.Write(stacks(false))
		}
		// Write the stack trace for all goroutines to the files.
		trace := stacks(true)
		logExitFunc = func(error) {} // If we get a write error, we'll still exit below.
		for log := LevelFatal; log >= LevelInfo; log-- {
			if f := l.file[log]; f != nil { // Can be nil if -logtostderr is set.
				f.Write(trace)
			}
		}
		l.mu.Unlock()
		l.timeoutFlush(10 * time.Second)
		os.Exit(255) // C++ uses -1, which is silly because it's anded with 255 anyway.
	}
	l.putBuffer(buf)
	l.mu.Unlock()
	if stats := l.severityStats[s]; stats != nil {
		atomic.AddInt64(&stats.lines, 1)
		atomic.AddInt64(&stats.bytes, int64(len(data)))
	}
}

// timeoutFlush calls Flush and returns when it completes or after timeout
// elapses, whichever happens first.  This is needed because the hooks invoked
// by Flush may deadlock when glog.Fatal is called from a hook that holds
// a lock.
func (l *Logger) timeoutFlush(timeout time.Duration) {
	done := make(chan bool, 1)
	go func() {
		l.Flush() // calls logging.lockAndFlushAll()
		done <- true
	}()
	select {
	case <-done:
	case <-time.After(timeout):
		fmt.Fprintln(os.Stderr, "glog: Flush took longer than", timeout)
	}
}

// stacks is a wrapper for runtime.Stack that attempts to recover the data for all goroutines.
func stacks(all bool) []byte {
	// We don't know how big the traces are, so grow a few times if they don't fit. Start large, though.
	n := 10000
	if all {
		n = 100000
	}
	var trace []byte
	for i := 0; i < 5; i++ {
		trace = make([]byte, n)
		nbytes := runtime.Stack(trace, all)
		if nbytes < len(trace) {
			return trace[:nbytes]
		}
		n *= 2
	}
	return trace
}

// logExitFunc provides a simple mechanism to override the default behavior
// of exiting on error. Used in testing and to guarantee we reach a required exit
// for fatal logs. Instead, exit could be a function rather than a method but that
// would make its use clumsier.
var logExitFunc func(error)

// exit is called if there is trouble creating or writing log files.
// It flushes the logs and exits the program; there's no point in hanging around.
// l.mu is held.
func (l *Logger) exit(err error) {
	fmt.Fprintf(os.Stderr, "log: exiting because of error: %s\n", err)
	// If logExitFunc is set, we do that instead of exiting.
	if logExitFunc != nil {
		logExitFunc(err)
		return
	}
	l.flushAll()
	os.Exit(2)
}

// syncBuffer joins a bufio.Writer to its underlying file, providing access to the
// file's Sync method and providing a wrapper for the Write method that provides log
// file rotation. There are conflicting methods, so the file cannot be embedded.
// l.mu is held for all its methods.
type syncBuffer struct {
	logger *Logger
	*bufio.Writer
	file   *os.File
	sev    Severity
	nbytes uint64 // The number of bytes written to this file
}

func (sb *syncBuffer) Sync() error {
	return sb.file.Sync()
}

func (sb *syncBuffer) Write(p []byte) (n int, err error) {
	if sb.nbytes+uint64(len(p)) >= MaxSize {
		if err := sb.rotateFile(time.Now()); err != nil {
			sb.logger.exit(err)
		}
	}
	n, err = sb.Writer.Write(p)
	sb.nbytes += uint64(n)
	if err != nil {
		sb.logger.exit(err)
	}
	return
}

// rotateFile closes the syncBuffer's file and starts a new one.
func (sb *syncBuffer) rotateFile(now time.Time) error {
	if sb.file != nil {
		sb.Flush()
		sb.file.Close()
	}
	var err error
	sb.file, _, err = create(sb.logger.logname, severityName[sb.sev], now)
	sb.nbytes = 0
	if err != nil {
		return err
	}

	sb.Writer = bufio.NewWriterSize(sb.file, bufferSize)

	// Write header.
	var buf bytes.Buffer
	fmt.Fprintf(&buf, "Log file created at: %s\n", now.Format("2006/01/02 15:04:05"))
	fmt.Fprintf(&buf, "Running on machine: %s\n", host)
	fmt.Fprintf(&buf, "Binary: Built with %s %s for %s/%s\n", runtime.Compiler, runtime.Version(), runtime.GOOS, runtime.GOARCH)
	fmt.Fprintf(&buf, "Log line format: [IWEF]mmdd hh:mm:ss.uuuuuu threadid file:line] msg\n")
	n, err := sb.file.Write(buf.Bytes())
	sb.nbytes += uint64(n)
	return err
}

// bufferSize sizes the buffer associated with each log file. It's large
// so that log records can accumulate without the logging thread blocking
// on disk I/O. The flushDaemon will block instead.
const bufferSize = 256 * 1024

// createFiles creates all the log files for severity from sev down to LevelInfo.
// l.mu is held.
func (l *Logger) createFiles(sev Severity) error {
	now := time.Now()
	// Files are created in decreasing severity order, so as soon as we find one
	// has already been created, we can stop.
	for s := sev; s >= LevelInfo && l.file[s] == nil; s-- {
		sb := &syncBuffer{
			logger: l,
			sev:    s,
		}
		if err := sb.rotateFile(now); err != nil {
			return err
		}
		l.file[s] = sb
	}
	return nil
}

const flushInterval = 30 * time.Second

// flushDaemon periodically flushes the log file buffers.
func (l *Logger) flushDaemon() {
	defer close(l.stopped)
	ticker := time.NewTicker(flushInterval)
	tc := ticker.C
	defer ticker.Stop()
	for {
		select {
		case <-tc:
			l.lockAndFlushAll()
		case <-l.stop:
			return
		}
	}
}

// lockAndFlushAll is like flushAll but locks l.mu first.
func (l *Logger) lockAndFlushAll() {
	l.mu.Lock()
	l.flushAll()
	l.mu.Unlock()
}

// flushAll flushes all the logs and attempts to "sync" their data to disk.
// l.mu is held.
func (l *Logger) flushAll() {
	// Flush from fatal down, in case there's trouble flushing.
	for s := LevelFatal; s >= LevelInfo; s-- {
		file := l.file[s]
		if file != nil {
			file.Flush() // ignore error
			file.Sync()  // ignore error
		}
	}
}

// CopyStandardLogTo arranges for messages written to the Go "log" package's
// default logs to also appear in the Google logs for the named and lower
// severities.  Subsequent changes to the standard log's default output location
// or format may break this behavior.
//
// Valid names are "INFO", "WARNING", "ERROR", and "FATAL".  If the name is not
// recognized, CopyStandardLogTo panics.
func (l *Logger) CopyStandardLogTo(name string) {
	sev, ok := severityByName(name)
	if !ok {
		panic(fmt.Sprintf("log.CopyStandardLogTo(%q): unrecognized severity name", name))
	}
	// Set a log format that captures the user's file and line:
	//   d.go:23: message
	stdLog.SetFlags(stdLog.Lshortfile)
	stdLog.SetOutput(logBridge{logging: l, severity: sev})
}

// logBridge provides the Write method that enables CopyStandardLogTo to connect
// Go's standard logs to the logs provided by this package.
type logBridge struct {
	severity Severity
	logging  *Logger
}

// Write parses the standard logging line and passes its components to the
// logger for severity(lb).
func (lb logBridge) Write(b []byte) (n int, err error) {
	var (
		file = "???"
		line = 1
		text string
	)
	// Split "d.go:23: message" into "d.go", "23", and "message".
	if parts := bytes.SplitN(b, []byte{':'}, 3); len(parts) != 3 || len(parts[0]) < 1 || len(parts[2]) < 1 {
		text = fmt.Sprintf("bad log format: %s", b)
	} else {
		file = string(parts[0])
		text = string(parts[2][1:]) // skip leading space
		line, err = strconv.Atoi(string(parts[1]))
		if err != nil {
			text = fmt.Sprintf("bad line number: %s", b)
			line = 1
		}
	}
	// printWithFileLine with alsoToStderr=true, so standard log messages
	// always appear on standard error.
	lb.logging.printWithFileLine(lb.severity, file, line, true, text)
	return len(b), nil
}

// setV computes and remembers the V level for a given PC
// when vmodule is enabled.
// File pattern matching takes the basename of the file, stripped
// of its .go suffix, and uses filepath.Match, which is a little more
// general than the *? matching used in C++.
// l.mu is held.
func (l *Logger) setV(pc uintptr) Level {
	fn := runtime.FuncForPC(pc)
	file, _ := fn.FileLine(pc)
	// The file is something like /a/b/c/d.go. We want just the d.
	if strings.HasSuffix(file, ".go") {
		file = file[:len(file)-3]
	}
	if slash := strings.LastIndex(file, "/"); slash >= 0 {
		file = file[slash+1:]
	}
	for _, filter := range l.vmodule.filter {
		if filter.match(file) {
			l.vmap[pc] = filter.level
			return filter.level
		}
	}
	l.vmap[pc] = 0
	return 0
}

// V reports whether verbosity at the call site is at least the requested level.
// The returned value is a pointer to the receiver, which is nil if the requested level
// is not set.
// Thus, one may write either
//	if glog.V(2) != nil { l.Info("log this") }
// or
//	glog.V(2).Info("log this")
// The second form is shorter but the first is cheaper if logging is off because it does
// not evaluate its arguments.
//
// Whether an individual call to V generates a log record depends on the setting of
// the Verbosity and VModule options; both are off by default. If the level in the call to
// V is at least the value of Verbosity, or of VModule for the source file containing the
// call, the V call will return l.
//
// NOTE: This is a deviation from previous github.com/golang/glog behavior in that it is less
// convenient to use V(L). This is a compromise made in removing all global state from glog.
func (l *Logger) V(level Level) *Logger {
	// This function tries hard to be cheap unless there's work to do.
	// The fast path is two atomic loads and compares.
	if l == nil {
		return nil
	}

	// Here is a cheap but safe test to see if V logging is enabled globally.
	if l.verbosity.get() >= level {
		return l
	}

	// It's off globally but it vmodule may still be set.
	// Here is another cheap but safe test to see if vmodule is enabled.
	if atomic.LoadInt32(&l.filterLength) > 0 {
		// Now we need a proper lock to use the logging structure. The pcs field
		// is shared so we must lock before accessing it. This is fairly expensive,
		// but if V logging is enabled we're slow anyway.
		l.mu.Lock()
		defer l.mu.Unlock()
		if runtime.Callers(2, l.pcs[:]) == 0 {
			return nil
		}
		v, ok := l.vmap[l.pcs[0]]
		if !ok {
			v = l.setV(l.pcs[0])
		}
		if v >= level {
			return l
		}
	}
	return nil
}

// Print logs to the configured Print level (from Options).
// Arguments are handled in the manner of fmt.Print; a newline is appended if missing.
func (l *Logger) Print(args ...interface{}) {
	if l != nil {
		l.print(l.printLevel.get(), args...)
	}
}

// PrintDepth acts as Print but uses depth to determine which call frame to log.
// PrintDepth(0, "msg") is the same as Print("msg").
func (l *Logger) PrintDepth(depth int, args ...interface{}) {
	if l != nil {
		l.printDepth(l.printLevel.get(), depth, args...)
	}
}

// Println logs to the configured Print level (from Options).
// Arguments are handled in the manner of fmt.Println; a newline is appended if missing.
func (l *Logger) Println(args ...interface{}) {
	if l != nil {
		l.println(l.printLevel.get(), args...)
	}
}

// Printf logs to the configured Print level (from Options).
// Arguments are handled in the manner of fmt.Printf; a newline is appended if missing.
func (l *Logger) Printf(format string, args ...interface{}) {
	if l != nil {
		l.printf(l.printLevel.get(), format, args...)
	}
}

// Info logs to the INFO log.
// Arguments are handled in the manner of fmt.Print; a newline is appended if missing.
func (l *Logger) Info(args ...interface{}) {
	if l != nil {
		l.print(LevelInfo, args...)
	}
}

// InfoDepth acts as Info but uses depth to determine which call frame to log.
// InfoDepth(0, "msg") is the same as Info("msg").
func (l *Logger) InfoDepth(depth int, args ...interface{}) {
	if l != nil {
		l.printDepth(LevelInfo, depth, args...)
	}
}

// Infoln logs to the INFO log.
// Arguments are handled in the manner of fmt.Println; a newline is appended if missing.
func (l *Logger) Infoln(args ...interface{}) {
	if l != nil {
		l.println(LevelInfo, args...)
	}
}

// Infof logs to the INFO log.
// Arguments are handled in the manner of fmt.Printf; a newline is appended if missing.
func (l *Logger) Infof(format string, args ...interface{}) {
	if l != nil {
		l.printf(LevelInfo, format, args...)
	}
}

// Warning logs to the WARNING and INFO logs.
// Arguments are handled in the manner of fmt.Print; a newline is appended if missing.
func (l *Logger) Warning(args ...interface{}) {
	if l != nil {
		l.print(LevelWarning, args...)
	}
}

// WarningDepth acts as Warning but uses depth to determine which call frame to log.
// WarningDepth(0, "msg") is the same as Warning("msg").
func (l *Logger) WarningDepth(depth int, args ...interface{}) {
	if l != nil {
		l.printDepth(LevelWarning, depth, args...)
	}
}

// Warningln logs to the WARNING and INFO logs.
// Arguments are handled in the manner of fmt.Println; a newline is appended if missing.
func (l *Logger) Warningln(args ...interface{}) {
	if l != nil {
		l.println(LevelWarning, args...)
	}
}

// Warningf logs to the WARNING and INFO logs.
// Arguments are handled in the manner of fmt.Printf; a newline is appended if missing.
func (l *Logger) Warningf(format string, args ...interface{}) {
	if l != nil {
		l.printf(LevelWarning, format, args...)
	}
}

// Error logs to the ERROR, WARNING, and INFO logs.
// Arguments are handled in the manner of fmt.Print; a newline is appended if missing.
func (l *Logger) Error(args ...interface{}) {
	if l != nil {
		l.print(LevelError, args...)
	}
}

// ErrorDepth acts as Error but uses depth to determine which call frame to log.
// ErrorDepth(0, "msg") is the same as Error("msg").
func (l *Logger) ErrorDepth(depth int, args ...interface{}) {
	if l != nil {
		l.printDepth(LevelError, depth, args...)
	}
}

// Errorln logs to the ERROR, WARNING, and INFO logs.
// Arguments are handled in the manner of fmt.Println; a newline is appended if missing.
func (l *Logger) Errorln(args ...interface{}) {
	if l != nil {
		l.println(LevelError, args...)
	}
}

// Errorf logs to the ERROR, WARNING, and INFO logs.
// Arguments are handled in the manner of fmt.Printf; a newline is appended if missing.
func (l *Logger) Errorf(format string, args ...interface{}) {
	if l != nil {
		l.printf(LevelError, format, args...)
	}
}

// Fatal logs to the FATAL, ERROR, WARNING, and INFO logs,
// including a stack trace of all running goroutines, then calls os.Exit(255).
// Arguments are handled in the manner of fmt.Print; a newline is appended if missing.
func (l *Logger) Fatal(args ...interface{}) {
	if l != nil {
		l.print(LevelFatal, args...)
	}
	// There is no logger, just exit outright:
	os.Exit(255)
}

// FatalDepth acts as Fatal but uses depth to determine which call frame to log.
// FatalDepth(0, "msg") is the same as Fatal("msg").
func (l *Logger) FatalDepth(depth int, args ...interface{}) {
	if l != nil {
		l.printDepth(LevelFatal, depth, args...)
	}
	os.Exit(255)
}

// Fatalln logs to the FATAL, ERROR, WARNING, and INFO logs,
// including a stack trace of all running goroutines, then calls os.Exit(255).
// Arguments are handled in the manner of fmt.Println; a newline is appended if missing.
func (l *Logger) Fatalln(args ...interface{}) {
	if l != nil {
		l.println(LevelFatal, args...)
	}
	os.Exit(255)
}

// Fatalf logs to the FATAL, ERROR, WARNING, and INFO logs,
// including a stack trace of all running goroutines, then calls os.Exit(255).
// Arguments are handled in the manner of fmt.Printf; a newline is appended if missing.
func (l *Logger) Fatalf(format string, args ...interface{}) {
	if l != nil {
		l.printf(LevelFatal, format, args...)
	}
	os.Exit(255)
}

// fatalNoStacks is non-zero if we are to exit without dumping goroutine stacks.
// It allows Exit and relatives to use the Fatal logs.
//
// This is not part of loggingT since, no matter what, we're exiting.
var fatalNoStacks uint32

// Exit logs to the FATAL, ERROR, WARNING, and INFO logs, then calls os.Exit(1).
// Arguments are handled in the manner of fmt.Print; a newline is appended if missing.
func (l *Logger) Exit(args ...interface{}) {
	if l != nil {
		atomic.StoreUint32(&fatalNoStacks, 1)
		l.print(LevelFatal, args...)
	}
	// There is no logger, just exit outright:
	os.Exit(1)
}

// ExitDepth acts as Exit but uses depth to determine which call frame to log.
// ExitDepth(0, "msg") is the same as Exit("msg").
func (l *Logger) ExitDepth(depth int, args ...interface{}) {
	if l != nil {
		atomic.StoreUint32(&fatalNoStacks, 1)
		l.printDepth(LevelFatal, depth, args...)
	}
	os.Exit(1)
}

// Exitln logs to the FATAL, ERROR, WARNING, and INFO logs, then calls os.Exit(1).
func (l *Logger) Exitln(args ...interface{}) {
	if l != nil {
		atomic.StoreUint32(&fatalNoStacks, 1)
		l.println(LevelFatal, args...)
	}
	os.Exit(1)
}

// Exitf logs to the FATAL, ERROR, WARNING, and INFO logs, then calls os.Exit(1).
// Arguments are handled in the manner of fmt.Printf; a newline is appended if missing.
func (l *Logger) Exitf(format string, args ...interface{}) {
	if l != nil {
		atomic.StoreUint32(&fatalNoStacks, 1)
		l.printf(LevelFatal, format, args...)
	}
}
