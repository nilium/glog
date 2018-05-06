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

package glog

import (
	"bytes"
	"flag"
	"fmt"
	stdLog "log"
	"path/filepath"
	"runtime"
	"strconv"
	"strings"
	"testing"
	"time"
)

func newLog(t testing.TB) *Logger {
	l, err := NewLog(NewOptions())
	if err != nil {
		t.Fatalf("unable to create log: %v", err)
	}
	if l == nil {
		t.Fatalf("log is nil")
	}
	return l
}

func TestMain(m *testing.M) {
	flag.Parse()

	m.Run()
}

// Test that shortHostname works as advertised.
func TestShortHostname(t *testing.T) {
	for hostname, expect := range map[string]string{
		"":                "",
		"host":            "host",
		"host.google.com": "host",
	} {
		if got := shortHostname(hostname); expect != got {
			t.Errorf("shortHostname(%q): expected %q, got %q", hostname, expect, got)
		}
	}
}

// flushBuffer wraps a bytes.Buffer to satisfy flushSyncWriter.
type flushBuffer struct {
	bytes.Buffer
}

func (f *flushBuffer) Flush() error {
	return nil
}

func (f *flushBuffer) Sync() error {
	return nil
}

// swap sets the log writers and returns the old array.
func (l *Logger) swap(writers [numSeverity]flushSyncWriter) (old [numSeverity]flushSyncWriter) {
	l.mu.Lock()
	defer l.mu.Unlock()
	old = l.file
	for i, w := range writers {
		l.file[i] = w
	}
	return
}

// newBuffers sets the log writers to all new byte buffers and returns the old array.
func (l *Logger) newBuffers() [numSeverity]flushSyncWriter {
	return l.swap([numSeverity]flushSyncWriter{new(flushBuffer), new(flushBuffer), new(flushBuffer), new(flushBuffer)})
}

// contents returns the specified log value as a string.
func (l *Logger) contents(s Severity) string {
	return l.file[s].(*flushBuffer).String()
}

// contains reports whether the string is contained in the log.
func (l *Logger) contains(s Severity, str string, t *testing.T) bool {
	return strings.Contains(l.contents(s), str)
}

// Test that Info works as advertised.
func TestInfo(t *testing.T) {
	logging := newLog(t)
	defer logging.Close()
	defer logging.swap(logging.newBuffers())
	logging.Info("test")
	if !logging.contains(LevelInfo, "I", t) {
		t.Errorf("Info has wrong character: %q", logging.contents(LevelInfo))
	}
	if !logging.contains(LevelInfo, "test", t) {
		t.Error("Info failed")
	}
}

func TestInfoDepth(t *testing.T) {
	logging := newLog(t)
	defer logging.Close()
	defer logging.swap(logging.newBuffers())

	f := func() { logging.InfoDepth(1, "depth-test1") }

	// The next three lines must stay together
	_, _, wantLine, _ := runtime.Caller(0)
	logging.InfoDepth(0, "depth-test0")
	f()

	msgs := strings.Split(strings.TrimSuffix(logging.contents(LevelInfo), "\n"), "\n")
	if len(msgs) != 2 {
		t.Fatalf("Got %d lines, expected 2", len(msgs))
	}

	for i, m := range msgs {
		if !strings.HasPrefix(m, "I") {
			t.Errorf("InfoDepth[%d] has wrong character: %q", i, m)
		}
		w := fmt.Sprintf("depth-test%d", i)
		if !strings.Contains(m, w) {
			t.Errorf("InfoDepth[%d] missing %q: %q", i, w, m)
		}

		// pull out the line number (between : and ])
		msg := m[strings.LastIndex(m, ":")+1:]
		x := strings.Index(msg, "]")
		if x < 0 {
			t.Errorf("InfoDepth[%d]: missing ']': %q", i, m)
			continue
		}
		line, err := strconv.Atoi(msg[:x])
		if err != nil {
			t.Errorf("InfoDepth[%d]: bad line number: %q", i, m)
			continue
		}
		wantLine++
		if wantLine != line {
			t.Errorf("InfoDepth[%d]: got line %d, want %d", i, line, wantLine)
		}
	}
}

// Test that CopyStandardLogTo panics on bad input.
func TestCopyStandardLogToPanic(t *testing.T) {
	logging := newLog(t)
	defer logging.Close()
	defer func() {
		if s, ok := recover().(string); !ok || !strings.Contains(s, "LOG") {
			t.Errorf(`CopyStandardLogTo("LOG") should have panicked: %v`, s)
		}
	}()
	logging.CopyStandardLogTo("LOG")
}

// Test that using the standard log package logs to INFO.
func TestStandardLog(t *testing.T) {
	logging := newLog(t)
	logging.CopyStandardLogTo("INFO")
	defer logging.Close()
	defer logging.swap(logging.newBuffers())
	stdLog.Print("test")
	if !logging.contains(LevelInfo, "I", t) {
		t.Errorf("Info has wrong character: %q", logging.contents(LevelInfo))
	}
	if !logging.contains(LevelInfo, "test", t) {
		t.Error("Info failed")
	}
}

// Test that the header has the correct format.
func TestHeader(t *testing.T) {
	logging := newLog(t)
	defer logging.Close()
	defer logging.swap(logging.newBuffers())
	defer func(previous func() time.Time) { timeNow = previous }(timeNow)
	timeNow = func() time.Time {
		return time.Date(2006, 1, 2, 15, 4, 5, .067890e9, time.Local)
	}
	pid = 1234
	logging.Info("test")
	var line int
	format := "I0102 15:04:05.067890    1234 glog_test.go:%d] test\n"
	n, err := fmt.Sscanf(logging.contents(LevelInfo), format, &line)
	if n != 1 || err != nil {
		t.Errorf("log format error: %d elements, error %s:\n%s", n, err, logging.contents(LevelInfo))
	}
	// Scanf treats multiple spaces as equivalent to a single space,
	// so check for correct space-padding also.
	want := fmt.Sprintf(format, line)
	if logging.contents(LevelInfo) != want {
		t.Errorf("log format error: got:\n\t%q\nwant:\t%q", logging.contents(LevelInfo), want)
	}
}

// Test that an Error log goes to Warning and Info.
// Even in the Info log, the source character will be E, so the data should
// all be identical.
func TestError(t *testing.T) {
	logging := newLog(t)
	defer logging.Close()
	defer logging.swap(logging.newBuffers())
	logging.Error("test")
	if !logging.contains(LevelError, "E", t) {
		t.Errorf("Error has wrong character: %q", logging.contents(LevelError))
	}
	if !logging.contains(LevelError, "test", t) {
		t.Error("Error failed")
	}
	str := logging.contents(LevelError)
	if !logging.contains(LevelWarning, str, t) {
		t.Error("Warning failed")
	}
	if !logging.contains(LevelInfo, str, t) {
		t.Error("Info failed")
	}
}

// Test that a Warning log goes to Info.
// Even in the Info log, the source character will be W, so the data should
// all be identical.
func TestWarning(t *testing.T) {
	logging := newLog(t)
	defer logging.Close()
	defer logging.swap(logging.newBuffers())
	logging.Warning("test")
	if !logging.contains(LevelWarning, "W", t) {
		t.Errorf("Warning has wrong character: %q", logging.contents(LevelWarning))
	}
	if !logging.contains(LevelWarning, "test", t) {
		t.Error("Warning failed")
	}
	str := logging.contents(LevelWarning)
	if !logging.contains(LevelInfo, str, t) {
		t.Error("Info failed")
	}
}

// Test that a Print goes to the correct log.
func TestPrint(t *testing.T) {
	logging := newLog(t)
	defer logging.Close()
	defer logging.swap(logging.newBuffers())
	logging.SetPrintLevel(LevelInfo)
	logging.Print("test-info")
	if !logging.contains(LevelInfo, "I", t) {
		t.Errorf("Info has wrong character: %q", logging.contents(LevelInfo))
	}
	if !logging.contains(LevelInfo, "test-info", t) {
		t.Error("Printing to Info failed")
	}

	// Move to warning
	logging.SetPrintLevel(LevelWarning)
	logging.Print("test-warning")
	if !logging.contains(LevelWarning, "W", t) {
		t.Errorf("Warning has wrong character: %q", logging.contents(LevelInfo))
	}
	if !logging.contains(LevelWarning, "test-warning", t) {
		t.Error("Printing to Warning failed")
	}
	str := logging.contents(LevelWarning)
	if !logging.contains(LevelInfo, str, t) {
		t.Error("Info failed")
	}
}

// Test that a V log goes to Info.
func TestV(t *testing.T) {
	logging := newLog(t)
	defer logging.Close()
	defer logging.swap(logging.newBuffers())
	logging.SetVerbosity(2)
	logging.V(2).Info("test")
	if !logging.contains(LevelInfo, "I", t) {
		t.Errorf("Info has wrong character: %q", logging.contents(LevelInfo))
	}
	if !logging.contains(LevelInfo, "test", t) {
		t.Error("Info failed")
	}
}

// Test that a vmodule enables a log in this file.
func TestVmoduleOn(t *testing.T) {
	logging := newLog(t)
	defer logging.Close()
	defer logging.swap(logging.newBuffers())
	logging.SetVModule("glog_test=2")
	defer logging.SetVModule("")
	if logging.V(1) == nil {
		t.Error("V not enabled for 1")
	}
	if logging.V(2) == nil {
		t.Error("V not enabled for 2")
	}
	if logging.V(3) != nil {
		t.Error("V enabled for 3")
	}
	logging.V(2).Info("test")
	if !logging.contains(LevelInfo, "I", t) {
		t.Errorf("Info has wrong character: %q", logging.contents(LevelInfo))
	}
	if !logging.contains(LevelInfo, "test", t) {
		t.Error("Info failed")
	}
}

// Test that a vmodule of another file does not enable a log in this file.
func TestVmoduleOff(t *testing.T) {
	logging := newLog(t)
	defer logging.Close()
	defer logging.swap(logging.newBuffers())
	logging.SetVModule("notthisfile=2")
	for i := 1; i <= 3; i++ {
		if logging.V(Level(i)) != nil {
			t.Errorf("V enabled for %d", i)
		}
	}
	logging.V(2).Info("test")
	if logging.contents(LevelInfo) != "" {
		t.Error("V logged incorrectly")
	}
}

// vGlobs are patterns that match/don't match this file at V=2.
var vGlobs = map[string]bool{
	// Easy to test the numeric match here.
	"glog_test=1": false, // If -vmodule sets V to 1, V(2) will fail.
	"glog_test=2": true,
	"glog_test=3": true, // If -vmodule sets V to 1, V(3) will succeed.
	// These all use 2 and check the patterns. All are true.
	"*=2":           true,
	"?l*=2":         true,
	"????_*=2":      true,
	"??[mno]?_*t=2": true,
	// These all use 2 and check the patterns. All are false.
	"*x=2":         false,
	"m*=2":         false,
	"??_*=2":       false,
	"?[abc]?_*t=2": false,
}

// Test that vmodule globbing works as advertised.
func testVmoduleGlob(pat string, match bool, t *testing.T) {
	logging := newLog(t)
	defer logging.Close()
	defer logging.swap(logging.newBuffers())
	logging.SetVModule(pat)
	if (logging.V(2) != nil) != match {
		t.Errorf("incorrect match for %q: got %t expected %t", pat, logging.V(2) != nil, match)
	}
}

// Test that a vmodule globbing works as advertised.
func TestVmoduleGlob(t *testing.T) {
	for glob, match := range vGlobs {
		testVmoduleGlob(glob, match, t)
	}
}

func TestRollover(t *testing.T) {
	logging := newLog(t)
	defer logging.Close()
	var err error
	defer func(previous func(error)) { logExitFunc = previous }(logExitFunc)
	logExitFunc = func(e error) {
		err = e
	}
	defer func(previous uint64) { MaxSize = previous }(MaxSize)
	MaxSize = 512

	logging.Info("x") // Be sure we have a file.
	info, ok := logging.file[LevelInfo].(*syncBuffer)
	if !ok {
		t.Fatal("info wasn't created")
	}
	if err != nil {
		t.Fatalf("info has initial error: %v", err)
	}
	fname0 := info.file.Name()
	logging.Info(strings.Repeat("x", int(MaxSize))) // force a rollover
	if err != nil {
		t.Fatalf("info has error after big write: %v", err)
	}

	// Make sure the next log file gets a file name with a different
	// time stamp.
	//
	// TODO: determine whether we need to support subsecond log
	// rotation.  C++ does not appear to handle this case (nor does it
	// handle Daylight Savings Time properly).
	time.Sleep(1 * time.Second)

	logging.Info("x") // create a new file
	if err != nil {
		t.Fatalf("error after rotation: %v", err)
	}
	fname1 := info.file.Name()
	if fname0 == fname1 {
		t.Errorf("info.f.Name did not change: %v", fname0)
	}
	if info.nbytes >= MaxSize {
		t.Errorf("file size was not reset: %d", info.nbytes)
	}
}

func TestLogBacktraceAt(t *testing.T) {
	logging := newLog(t)
	defer logging.Close()
	defer logging.swap(logging.newBuffers())
	// The peculiar style of this code simplifies line counting and maintenance of the
	// tracing block below.
	var infoLine string
	setTraceLocation := func(file string, line int, ok bool, delta int) {
		if !ok {
			t.Fatal("could not get file:line")
		}
		_, file = filepath.Split(file)
		infoLine = fmt.Sprintf("%s:%d", file, line+delta)
		err := logging.SetTraceLocation(infoLine)
		if err != nil {
			t.Fatal("error setting log_backtrace_at: ", err)
		}
	}
	{
		// Start of tracing block. These lines know about each other's relative position.
		_, file, line, ok := runtime.Caller(0)
		setTraceLocation(file, line, ok, +2) // Two lines between Caller and Info calls.
		logging.Info("we want a stack trace here")
	}
	numAppearances := strings.Count(logging.contents(LevelInfo), infoLine)
	if numAppearances < 2 {
		// Need 2 appearances, one in the log header and one in the trace:
		//   log_test.go:281: I0511 16:36:06.952398 02238 log_test.go:280] we want a stack trace here
		//   ...
		//   github.com/glog/glog_test.go:280 (0x41ba91)
		//   ...
		// We could be more precise but that would require knowing the details
		// of the traceback format, which may not be dependable.
		t.Fatal("got no trace back; log is ", logging.contents(LevelInfo))
	}
}

func BenchmarkHeader(b *testing.B) {
	logging := newLog(b)
	defer logging.Close()
	b.ResetTimer()
	for i := 0; i < b.N; i++ {
		buf, _, _ := logging.header(LevelInfo, 0)
		logging.putBuffer(buf)
	}
	b.StopTimer()
}
