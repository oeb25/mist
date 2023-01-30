/**
 * @license
 * Copyright 2015 The Emscripten Authors
 * SPDX-License-Identifier: MIT
 */
"use strict";var Module={},ENVIRONMENT_IS_NODE="object"==typeof process&&"object"==typeof process.versions&&"string"==typeof process.versions.node;if(ENVIRONMENT_IS_NODE){var nodeWorkerThreads=require("worker_threads"),parentPort=nodeWorkerThreads.parentPort;parentPort.on("message",(function(e){onmessage({data:e})}));var fs=require("fs");Object.assign(global,{self:global,require:require,Module:Module,location:{href:__filename},Worker:nodeWorkerThreads.Worker,importScripts:function(e){(0,eval)(fs.readFileSync(e,"utf8"))},postMessage:function(e){parentPort.postMessage(e)},performance:global.performance||{now:function(){return Date.now()}}})}var initializedJS=!1,pendingNotifiedProxyingQueues=[];function assert(e,r){e||abort("Assertion failed: "+r)}function threadPrintErr(){var e=Array.prototype.slice.call(arguments).join(" ");ENVIRONMENT_IS_NODE?fs.writeSync(2,e+"\n"):console.error(e)}function threadAlert(){var e=Array.prototype.slice.call(arguments).join(" ");postMessage({cmd:"alert",text:e,threadId:Module._pthread_self()})}var out=()=>{throw"out() is not defined in worker.js."},err=threadPrintErr;self.alert=threadAlert,Module.instantiateWasm=(e,r)=>{var t=new WebAssembly.Instance(Module.wasmModule,e);return r(t),Module.wasmModule=null,t.exports},self.onmessage=e=>{try{if("load"===e.data.cmd){if(Module.wasmModule=e.data.wasmModule,Module.wasmMemory=e.data.wasmMemory,Module.buffer=Module.wasmMemory.buffer,Module.ENVIRONMENT_IS_PTHREAD=!0,"string"==typeof e.data.urlOrBlob)importScripts(e.data.urlOrBlob);else{var r=URL.createObjectURL(e.data.urlOrBlob);importScripts(r),URL.revokeObjectURL(r)}initZ3(Module).then((function(e){Module=e}))}else if("run"===e.data.cmd){Module.__performance_now_clock_drift=performance.now()-e.data.time,Module.__emscripten_thread_init(e.data.threadInfoStruct,0,0,1),assert(e.data.threadInfoStruct),Module.establishStackSpace(),Module.PThread.receiveObjectTransfer(e.data),Module.PThread.threadInitTLS(),initializedJS||(pendingNotifiedProxyingQueues.forEach((e=>{Module.executeNotifiedProxyingQueue(e)})),pendingNotifiedProxyingQueues=[],initializedJS=!0);try{Module.invokeEntryPoint(e.data.start_routine,e.data.arg)}catch(e){if("unwind"!=e){if(!(e instanceof Module.ExitStatus))throw e;Module.keepRuntimeAlive()?err("Pthread 0x"+Module._pthread_self().toString(16)+" called exit(), staying alive due to noExitRuntime."):(err("Pthread 0x"+Module._pthread_self().toString(16)+" called exit(), calling _emscripten_thread_exit."),Module.__emscripten_thread_exit(e.status))}else err("Pthread 0x"+Module._pthread_self().toString(16)+" completed its main entry point with an `unwind`, keeping the worker alive for asynchronous operation.")}}else"cancel"===e.data.cmd?Module._pthread_self()&&Module.__emscripten_thread_exit(-1):"setimmediate"===e.data.target||("processProxyingQueue"===e.data.cmd?initializedJS?Module.executeNotifiedProxyingQueue(e.data.queue):pendingNotifiedProxyingQueues.push(e.data.queue):(err("worker.js received unknown command "+e.data.cmd),err(e.data)))}catch(e){throw err("worker.js onmessage() captured an uncaught exception: "+e),e&&e.stack&&err(e.stack),Module.__emscripten_thread_crashed&&Module.__emscripten_thread_crashed(),e}};