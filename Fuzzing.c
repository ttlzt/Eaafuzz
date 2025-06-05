#define _GNU_SOURCE
#include <sys/time.h>
#include <stdio.h>
#include <stdlib.h>
#include <unistd.h> 
#include <unistd.h>
#include <fcntl.h> 
#include <errno.h>
#include <sys/resource.h>
#include <sys/wait.h>
#include <sched.h>
#include <sys/stat.h>
#include <string.h>
#include <sys/ipc.h>
#include <sys/shm.h>
#include <string.h>
#include <stdint.h>
#include <sys/mman.h>
#include <dirent.h>
#include <ctype.h>
#include <sys/socket.h>
#include <arpa/inet.h>
#include <netinet/in.h>
#include <time.h>
#include <stdbool.h>

/* Most of code is borrowed directly from AFL fuzzer (https://github.com/mirrorer/afl), credits to Michal Zalewski */

/* Fork server init timeout multiplier：我们将等待用户选择的超时加上这个时间，以便 fork 服务器启动。*/
#define FORK_WAIT_MULT      10
/* 用于将 SHM ID 传递给被调用程序的环境变量。 */
#define SHM_ENV_VAR "__AFL_SHM_ID"
/* 与 python 模块通信的本地端口. */
#define PORT                12012
/* 从 GCC 传递到 'as' 并用于解析配置文件的最大行长度。 */
#define MAX_LINE            8192
/* 为 forkserver 命令指定文件描述符（应用程序将使用 FORKSRV_FD 和 FORKSRV_FD + 1）。 */
#define FORKSRV_FD          198
/* 用于指示执行失败的独特位图签名。 */
#define EXEC_FAIL_SIG       0xfee1dead
/* CPU 负载和执行速度统计信息的平滑除数（1 - 无平滑）。 */
#define AVG_SMOOTHING       16
/* 用于 inserion 和 deletion 操作的区块大小的上限。这组数字会适应文件长度，默认情况下，最大文件长度为 10000。 */
/* 默认设置，稍后将根据文件 len 进行更改 */

#define N 10000

int havoc_blk_small = 2048;
int havoc_blk_medium = 4096;
int havoc_blk_large = 8192;
#define HAVOC_BLK_SMALL     2048
#define HAVOC_BLK_MEDIUM    4096
#define HAVOC_BLK_LARGE     7402
 
#define MAX_SIZE 10000  // 假设每个 tmp_ 数据块最大有1000个概率值
#define NUM_BLOCKS 30  // 一共有30个tmp_数据块
#define MAX_LINE_LENGTH 3000000 
 
#define MEM_BARRIER() \
    asm volatile("" ::: "memory")
/* 跟踪的二进制文件的 Map 大小。 */
#define MAP_SIZE            2<<18
 
#define R(x) (random() % (x))
#define likely(_x)   __builtin_expect(!!(_x), 1)
#define unlikely(_x)  __builtin_expect(!!(_x), 0)
#define MIN(_a,_b) ((_a) > (_b) ? (_b) : (_a))
#define MAX(_a,_b) ((_a) > (_b) ? (_a) : (_b))

/* 对 read（） 和 write（） 版本进行错误检查，这些版本会根据需要调用 RPFATAL（）。 */
#define ck_write(fd, buf, len, fn) do { \
    u32 _len = (len); \
    int _res = write(fd, buf, _len); \
    if (_res != _len) fprintf(stderr, "Short write to %d %s\n",_res, fn); \
} while (0)
 
#define ck_read(fd, buf, len, fn) do { \
    u32 _len = (len); \
    int _res = read(fd, buf, _len); \
    if (_res != _len) fprintf(stderr, "Short read from %d %s\n",_res, fn[NUM_BLOCKS - 1]); \
} while (0)
 
/* 将面向 SER 的宏转换为 sprintf（） 到动态分配的缓冲区. */
#define alloc_printf(_str...) ({ \
    char* _tmp; \
    int _len = snprintf(NULL, 0, _str); \
    if (_len < 0) perror("Whoa, snprintf() fails?!"); \
    _tmp = malloc(_len + 1); \
    snprintf((char*)_tmp, _len + 1, _str); \
    _tmp; \
})


typedef uint8_t  u8;
typedef uint16_t u16;
typedef uint32_t u32;
#ifdef __x86_64__
typedef unsigned long long u64;
#else
typedef uint64_t u64;
#endif /* ^__x86_64__ */

unsigned long total_execs;              /* 执行总数 */
static int shm_id;                      /* SHM 区域的 ID */
static int mem_limit  = 1024;           /*目标程序的最大内存限制 */
static int cpu_aff = -1;                /* Selected CPU core */
int round_cnt = 0;                      /* 整数计数器 */
int edge_gain=0;                        /* 如果有新的边长 */
int exec_tmout = 1000;                  /* Exec 超时 （ms）                 */

int stage_num = 1;/*!!!!*/
int old=0;
int now=0;
int fast=1;
char * target_path;                     /* 目标二进制文件的路径          */
char * trace_bits;                      /* 带有插桩位图的 SHM */ 
static volatile int stop_soon;          /* Ctrl-C pressed?                  */
static int cpu_core_count;              /* CPU core count                   */
static u64 total_cal_us=0;              /* 总校准时间 （us）     */
static volatile int child_timed_out;    /* 跟踪的进程超时?        */
int kill_signal;                        /* 杀死子进程的信号    */
static int out_fd,                      /* out_file 的持久 fd       */
           dev_urandom_fd = -1,         /* /dev/urandom 的持久 fd   */
           dev_null_fd = -1,            /* /dev/null 的持久 fd      */
           fsrv_ctl_fd,                 /* Fork 服务器控制管道（写入） */
           fsrv_st_fd;                  /* Fork 服务器状态管道（读取）  */
static int forksrv_pid,                 /* fork 服务器的 PID           */
           child_pid = -1,              /* 模糊程序的 PID       */
           out_dir_fd = -1;             /* 锁定文件的 FD           */

char *in_dir,                           /* 包含测试用例的输入目录  */
     *out_file,                         /* File to fuzz（如果有）             */
     *out_dir;                          /* 工作和输出目录      */
char virgin_bits[MAP_SIZE];             /*尚未被模糊测试触及的区域 */
static int mut_cnt = 0;                 /* 总突变计数器          */
char *out_buf, *out_buf1, *out_buf2, *out_buf3;
size_t len;                             /* 每个更改的最大文件大小 */
double loc[10000];                        /* 用于存储关键字节位置的数组*/
int sign[10000];                        /* 用于存储关键字节符号的数组  */

/*更精细的 Grined 突变可能会有更好的结果，但速度更慢*/
//int num_index[23] = {0,2,4,8,16,32,64,128,256,512,1024,1536,2048,2560,3072, 3584,4096,4608,5120, 5632,6144,6656,7103};
/* default setting，会根据不同的文件长度而变化 */
int num_index[14] = {0,2,4,8,16,32,64,128,256,512,1024,2048,4096,8192};

enum {
  /* 00 */ FAULT_NONE,
  /* 01 */ FAULT_TMOUT,
  /* 02 */ FAULT_CRASH,
  /* 03 */ FAULT_ERROR,
  /* 04 */ FAULT_NOINST,
  /* 05 */ FAULT_NOBITS
};

/* Spin up fork server （仅限插桩模式）。这个想法解释如下：
   http://lcamtuf.blogspot.com/2014/10/fuzzing-binaries-without-execve.html
   从本质上讲，插桩允许我们跳过 execve（），而只保留
   克隆已停止的子项。因此，我们只执行一次，然后发送命令
   通过管道。此逻辑的另一部分位于 afl-as.h 中。 */
void setup_stdio_file(void) {

  char* fn = alloc_printf("%s/.cur_input", out_dir); // 使用 alloc_printf 函数创建一个字符串，该字符串是 out_dir 和 ".cur_input" 的连接。  out_dir 应该是在其他地方定义的输出目录路径。 alloc_printf 应该是一个自定义的函数，类似于 sprintf，但会动态分配内存。

  unlink(fn); /* Ignore errors */ // 删除名为 fn 的文件。  如果文件不存在，则忽略错误。

  out_fd = open(fn, O_RDWR | O_CREAT | O_EXCL, 0600); // 打开名为 fn 的文件，以读写模式 (O_RDWR) 打开。如果文件不存在，则创建 (O_CREAT)。 O_EXCL 确保如果文件已存在，则 open() 调用失败。  文件权限设置为 0600。  打开成功后，文件描述符存储在 out_fd 中。

  if (out_fd < 0) perror("Unable to create .cur_input"); // 如果打开文件失败，则打印错误消息到标准错误输出。

  free(fn); // 释放之前使用 alloc_printf 分配的内存。

}

/* 计算位图中设置的非 255 字节数。严格用于
   status 屏幕，每秒左右调用几次。统计测试输入质量 */
#define FF(_b)  (0xff << ((_b) << 3))
static u32 count_non_255_bytes(u8* mem) {

  u32* ptr = (u32*)mem;
  u32  i   = (MAP_SIZE >> 2);
  u32  ret = 0;

  while (i--) {

    u32 v = *(ptr++);

    /* 这是在原始位图上调用的，因此请针对最有可能的
       箱。 */

    if (v == 0xffffffff) continue;
    if ((v & FF(0)) != FF(0)) ret++;
    if ((v & FF(1)) != FF(1)) ret++;
    if ((v & FF(2)) != FF(2)) ret++;
    if ((v & FF(3)) != FF(3)) ret++;

  }

  return ret;

}

/* 处理停止信号（Ctrl-C 等）。 */

static void handle_stop_sig(int sig) {

  stop_soon = 1; 

  if (child_pid > 0) kill(child_pid, SIGKILL);
  if (forksrv_pid > 0) kill(forksrv_pid, SIGKILL);
  printf("total execs %ld edge coverage %d.\n", total_execs,(int)(count_non_255_bytes(virgin_bits)));
  
  //free buffer
  free(out_buf);
  free(out_buf1);
  free(out_buf2);
  free(out_buf3);
  exit(0);
}

/* 检查当前执行路径是否为表带来了任何新内容。
   更新 virgin bit 以反映发现。如果唯一的更改是
   特定元组的命中计数;如果看到新的 Tuples，则为 2。
   更新映射，因此后续调用将始终返回 0。
   这个函数在一个相当大的缓冲区上的每个 exec（） 之后调用，所以
   它需要快速。我们在 32 位和 64 位风格中执行此操作。 
   判断是否产生新的路径*/

static inline char has_new_bits(char* virgin_map) {

#ifdef __x86_64__

  u64* current = (u64*)trace_bits;
  u64* virgin  = (u64*)virgin_map;

  u32  i = (MAP_SIZE >> 3);

#else

  u32* current = (u32*)trace_bits;
  u32* virgin  = (u32*)virgin_map;

  u32  i = (MAP_SIZE >> 2);

#endif /* ^__x86_64__ */

  u8   ret = 0;

  while (i--) {

    /* 优化（*当前&*原始） == 0 - 即当前位图中没有位
       尚未从原始地图中清除 - 因为这将
       几乎总是如此。 */

    if (unlikely(*current) && unlikely(*current & *virgin)) {

      if (likely(ret < 2)) {

        u8* cur = (u8*)current;
        u8* vir = (u8*)virgin;

        /* 看起来我们还没有找到任何新字节;查看是否有任何非零
           current[] 中的字节在 virgin[] 中是原始的. */

#ifdef __x86_64__

        if ((cur[0] && vir[0] == 0xff) || (cur[1] && vir[1] == 0xff) ||
            (cur[2] && vir[2] == 0xff) || (cur[3] && vir[3] == 0xff) ||
            (cur[4] && vir[4] == 0xff) || (cur[5] && vir[5] == 0xff) ||
            (cur[6] && vir[6] == 0xff) || (cur[7] && vir[7] == 0xff)) ret = 2;
        else ret = 1;

#else

        if ((cur[0] && vir[0] == 0xff) || (cur[1] && vir[1] == 0xff) ||
            (cur[2] && vir[2] == 0xff) || (cur[3] && vir[3] == 0xff)) ret = 2;
        else ret = 1;

#endif /* ^__x86_64__ */

      }

      *virgin &= ~*current;

    }

    current++;
    virgin++;

  }

  return ret;

}


/* 句柄超时 （SIGALRM）终止执行时间超出预期的子进程 */

static void handle_timeout(int sig) {

  if (child_pid > 0) {

    child_timed_out = 1; 
    kill(child_pid, SIGKILL);

  } else if (child_pid == -1 && forksrv_pid > 0) {

    child_timed_out = 1; 
    kill(forksrv_pid, SIGKILL);

  }

}

/* 设置信号处理程序。这需要更复杂，因为 libc 开启
   Solaris 不恢复中断的读取（），SA_RESETHAND在调用
   siginterrupt（），并执行其他愚蠢的操作. 
   为程序设置信号处理函数，以便程序可以根据接收到的特定信号执行相应的处理逻辑。*/

void setup_signal_handlers(void) { // 定义一个名为 setup_signal_handlers 的函数，该函数不接受参数，也不返回任何值。

  struct sigaction sa; // 定义一个 sigaction 结构体变量 sa，用于配置信号处理方式。

  sa.sa_handler   = NULL; // 将 sa_handler 成员初始化为 NULL，表示暂时没有设置信号处理函数。
  sa.sa_flags     = SA_RESTART; // 设置 sa_flags 为 SA_RESTART，表示如果系统调用被信号中断，则在信号处理函数执行完毕后自动重启系统调用。
  sa.sa_sigaction = NULL; // 将 sa_sigaction 成员初始化为 NULL，因为这里使用 sa_handler 处理信号。
  sigemptyset(&sa.sa_mask); // 清空 sa_mask 成员，表示在信号处理函数执行期间不阻塞任何信号。


  /* 各种停止信号 */

  sa.sa_handler = handle_stop_sig; // 设置信号处理函数为 handle_stop_sig。
  sigaction(SIGHUP, &sa, NULL); // 注册 SIGHUP 信号的处理函数。  SIGHUP 通常表示挂起。
  sigaction(SIGINT, &sa, NULL); // 注册 SIGINT 信号的处理函数。 SIGINT 通常表示中断 (Ctrl+C)。
  sigaction(SIGTERM, &sa, NULL); // 注册 SIGTERM 信号的处理函数。 SIGTERM 通常表示终止请求。


  /* 执行超时通知 */

  sa.sa_handler = handle_timeout; // 设置信号处理函数为 handle_timeout。
  sigaction(SIGALRM, &sa, NULL); // 注册 SIGALRM 信号的处理函数。 SIGALRM 通常用于定时器超时。


  /* 我们不关心的信号 */

  sa.sa_handler = SIG_IGN; // 设置信号处理函数为 SIG_IGN，表示忽略该信号。
  sigaction(SIGTSTP, &sa, NULL); // 忽略 SIGTSTP 信号 (终端停止，Ctrl+Z)。
  sigaction(SIGPIPE, &sa, NULL); // 忽略 SIGPIPE 信号 (管道破裂，通常发生在写入已关闭的管道时)。

}
/*初始化模糊测试工具（如 AFL）使用的 fork 服务器，以高效地重复启动目标程序并对其进行测试。
通过 fork 服务器，模糊测试工具可以避免多次执行 execv() 带来的性能开销，从而更高效地测试目标程序的行为。*/
void init_forkserver(char** argv) {

  static struct itimerval it; // 静态变量，用于设置计时器。
  int st_pipe[2], ctl_pipe[2]; // 定义两个管道，st_pipe 用于状态通信，ctl_pipe 用于控制通信。
  int status; // 用于存储子进程状态。
  int rlen; // 用于存储读取的字节数。
  char* cwd = getcwd(NULL, 0); // 获取当前工作目录。
  out_file = alloc_printf("%s/%s/.cur_input",cwd, out_dir); // 创建输出文件路径。
  printf("Spinning up the fork server...\n"); // 打印信息，提示正在启动fork服务器。

  if (pipe(st_pipe) || pipe(ctl_pipe)) perror("pipe() failed"); // 创建两个管道，如果失败则打印错误信息。

  forksrv_pid = fork(); // 创建子进程。

  if (forksrv_pid < 0) perror("fork() failed"); // 检查fork是否成功。

  if (!forksrv_pid) { // 子进程代码块。

    struct rlimit r; // 用于设置资源限制。

    /* 乌普夫。在 OpenBSD 上，root 用户的默认 fd 限制设置为
       软 128.让我们试着修复它t... */

    if (!getrlimit(RLIMIT_NOFILE, &r) && r.rlim_cur < FORKSRV_FD + 2) { // 检查文件描述符限制，并在必要时增加。

      r.rlim_cur = FORKSRV_FD + 2;
      setrlimit(RLIMIT_NOFILE, &r); /* Ignore errors */ // 设置文件描述符限制，忽略错误。

    }

    if (mem_limit) { // 如果设置了内存限制，则设置内存限制。

      r.rlim_max = r.rlim_cur = ((rlim_t)mem_limit) << 20; // 设置最大和当前内存限制。

#ifdef RLIMIT_AS
      setrlimit(RLIMIT_AS, &r); /* Ignore errors */ // 设置虚拟内存限制。
#else
      /* 这解决了 OpenBSD，它没有 RLIMIT_AS，但
         根据可靠消息来源，RLIMIT_DATA 涵盖 Anonymous
         maps - 因此我们应该获得针对 OOM bug 的良好保护. */
      setrlimit(RLIMIT_DATA, &r); /* Ignore errors */ // 设置数据段大小限制。
#endif /* ^RLIMIT_AS */


    }

    /* 转储核心速度很慢，如果交付 SIGKILL，可能会导致异常
       在转储完成之前。 */

    r.rlim_max = r.rlim_cur = 0; // 禁止核心转储。

    setrlimit(RLIMIT_CORE, &r); /* Ignore errors */ // 设置核心转储限制。

    /* 隔离进程并配置标准描述符。如果 out_file 是
       指定，stdin 为 /dev/null;否则，将改为克隆 out_fd。 */

    setsid(); // 创建新的会话ID，使子进程成为会话组长。

    dup2(dev_null_fd, 1); // 重定向标准输出到 /dev/null。
    dup2(dev_null_fd, 2); // 重定向标准错误到 /dev/null。

    if (out_file) { // 如果 out_file 已设置。
      dup2(dev_null_fd, 0); // 重定向标准输入到 /dev/null。
    } else {
      dup2(out_fd, 0); // 重定向标准输入到 out_fd。
      close(out_fd); // 关闭 out_fd 的副本。
    }

    /* 设置控制和状态管道，关闭不需要的原始 fd. */

    if (dup2(ctl_pipe[0], FORKSRV_FD) < 0) perror("dup2() failed"); // 重定向控制管道到 FORKSRV_FD。
    if (dup2(st_pipe[1], FORKSRV_FD + 1) < 0) perror("dup2() failed"); // 重定向状态管道到 FORKSRV_FD + 1。

    close(ctl_pipe[0]); // 关闭不需要的管道端点。
    close(ctl_pipe[1]);
    close(st_pipe[0]);
    close(st_pipe[1]);

    close(out_dir_fd); // 关闭输出目录文件描述符。
    close(dev_null_fd); // 关闭 /dev/null 文件描述符。
    close(dev_urandom_fd); // 关闭 /dev/urandom 文件描述符。

    /* 这应该会稍微提高性能，因为它会阻止链接器
       在 fork（） 后做额外的工作。 */

    if (!getenv("LD_BIND_LAZY")) setenv("LD_BIND_NOW", "1", 0); // 设置环境变量 LD_BIND_NOW 为 1。

    execv(target_path, argv); // 执行目标程序。

    /*使用独特的位图签名告诉父级 execv（）
       Falling Through（失败）. */
    *(int *)trace_bits = EXEC_FAIL_SIG; // 如果 execv 失败，则设置 EXEC_FAIL_SIG 信号。
    exit(0); // 退出子进程。

  }

  /* 关闭不需要的终端节点。 */

  close(ctl_pipe[0]); // 关闭不需要的管道端点。
  close(st_pipe[1]);

  fsrv_ctl_fd = ctl_pipe[1]; // 保存控制管道文件描述符。
  fsrv_st_fd  = st_pipe[0]; // 保存状态管道文件描述符。

  /* 等待 fork 服务器启动，但不要等待太久。 */

  it.it_value.tv_sec = ((exec_tmout * FORK_WAIT_MULT) / 1000); // 设置计时器。
  it.it_value.tv_usec = ((exec_tmout * FORK_WAIT_MULT) % 1000) * 1000;

  setitimer(ITIMER_REAL, &it, NULL); // 启动计时器。

  rlen = read(fsrv_st_fd, &status, 4); // 读取状态管道。

  it.it_value.tv_sec = 0; // 停止计时器。
  it.it_value.tv_usec = 0;

  setitimer(ITIMER_REAL, &it, NULL);

  /*如果我们从服务器收到一条四字节的 “hello” 消息，则一切就绪。
     否则，请尝试找出问题所在. */

  if (rlen == 4) { // 检查是否成功连接。
    printf("All right - fork server is up."); // 打印成功信息。
    return;
  }

  if (child_timed_out) // 如果超时，则打印超时信息。
    perror("Timeout while initializing fork server (adjusting -t may help)");

  if (waitpid(forksrv_pid, &status, 0) <= 0) // 等待子进程结束。
    perror("waitpid() failed");

  if (WIFSIGNALED(status)) { // 检查子进程是否因信号终止。
    fprintf(stderr, "Fork server crashed with signal %d", WTERMSIG(status)); // 打印子进程终止信号。
  }

  if (*(int*)trace_bits == EXEC_FAIL_SIG) // 检查 execv 是否失败。
    fprintf(stderr, "Unable to execute target application ('%s')", argv[0]); // 打印 execv 失败信息。

  perror("Fork server handshake failed"); // 打印握手失败信息。

}

/* 摆脱共享内存 （atexit 处理程序）. */

static void remove_shm(void) {

  shmctl(shm_id, IPC_RMID, NULL);

}

/* 配置共享内存和virgin_bits。这在启动时调用. 
设置共享内存区域（Shared Memory, SHM），用于在模糊测试工具和目标程序之间共享覆盖率信息。*/

void setup_shm(void) {

  char* shm_str; // 定义一个字符指针，用于存储共享内存 ID 的字符串表示。

  memset(virgin_bits, 255, MAP_SIZE); // 将 virgin_bits 数组的 MAP_SIZE 个字节全部填充为 255。  这通常用于初始化标志位，表示共享内存的初始状态。  `virgin_bits` 和 `MAP_SIZE` 应该在代码的其他部分定义。

  shm_id = shmget(IPC_PRIVATE, MAP_SIZE, IPC_CREAT | IPC_EXCL | 0600); // 创建一个私有的共享内存段。

  if (shm_id < 0) perror("shmget() failed"); // 检查 shmget() 是否成功。如果失败，则输出错误信息。

  atexit(remove_shm); // 注册一个退出函数 remove_shm，该函数会在程序退出时被调用，用于删除共享内存段。  `remove_shm` 应该在代码的其他部分定义。

  shm_str = alloc_printf("%d", shm_id); // 使用 alloc_printf 将共享内存 ID 格式化为字符串。  `alloc_printf` 应该是一个自定义函数，用于动态分配内存以存储格式化后的字符串。

  /* 如果有人要求我们在 dumb 模式下对插桩的二进制文件进行模糊测试，
     我们不希望它们检测 instrumentation，因为我们不会发送
     fork server 命令。这应该被更好的自动检测所取代
     也许以后呢？ */

  setenv(SHM_ENV_VAR, shm_str, 1); // 将共享内存 ID 设置为环境变量。  `SHM_ENV_VAR` 和 `shm_str` 应该是已知的常量或变量。  这个设置很有可能与程序的其他部分进行交互，以便其他部分可以使用这个共享内存。

  free(shm_str); // 释放之前分配的 shm_str 的内存。

  trace_bits = shmat(shm_id, NULL, 0); // 将共享内存段映射到当前进程的地址空间。

  if (!trace_bits) perror("shmat() failed"); // 检查 shmat() 是否成功。如果失败，则输出错误信息。

}
/*设置必要的输出目录和文件描述符，为工具的正常运行做好准备。*/
void setup_dirs_fds(void) {

  char* tmp; // 声明一个字符指针，虽然声明了但未使用，可能是一个残留代码或后续开发的占位符。
  int fd;    // 声明一个整数变量，用于存储文件描述符，同样未使用。

  printf("Setting up output directories..."); // 打印消息，提示正在设置输出目录。

  if (mkdir(out_dir, 0700)) { // 尝试创建名为 out_dir 的目录，权限为 0700。

    if (errno != EEXIST) fprintf(stderr,"Unable to create %s\n", out_dir); // 如果 mkdir 失败且错误不是因为目录已存在 (EEXIST)，则打印错误消息到标准错误输出。

  }

  /* 通常有用的文件描述符。 */

  dev_null_fd = open("/dev/null", O_RDWR); // 打开 /dev/null 文件，以读写模式 (O_RDWR)。
  if (dev_null_fd < 0) perror("Unable to open /dev/null"); // 如果打开失败，则打印错误信息到标准错误输出。

  dev_urandom_fd = open("/dev/urandom", O_RDONLY); // 打开 /dev/urandom 文件，以只读模式 (O_RDONLY)。
  if (dev_urandom_fd < 0) perror("Unable to open /dev/urandom"); // 如果打开失败，则打印错误信息到标准错误输出。

}

/* Detect @@ in args.
检测传入程序的参数列表（argv）中是否包含特殊占位符 @@，
并将其替换为实际文件路径，以便模糊测试工具能够正确地运行目标程序。 */

void detect_file_args(char** argv) {

  int i = 0; // 循环计数器，用于遍历命令行参数。
  char* cwd = getcwd(NULL, 0); // 获取当前工作目录，并将结果存储在 cwd 中。 getcwd(NULL, 0) 会自动分配内存。

  if (!cwd) perror("getcwd() failed"); // 检查 getcwd 是否成功。如果失败，则打印错误信息并终止程序。

  while (argv[i]) { // 循环遍历命令行参数，直到遇到 NULL (argv 的结尾)。

    char* aa_loc = strstr(argv[i], "@@"); // 在当前参数中查找 "@@" 子串。  如果找到，aa_loc 将指向 "@@" 的第一个字符。

    if (aa_loc) { // 如果找到 "@@"

      char *aa_subst, *n_arg; // 声明两个字符指针，用于存储替换字符串和新的参数字符串。

      /* 如果我们还没有选择文件名，请使用 safe default. */

      if (!out_file) // 如果 out_file 为空指针 (未设置)，
        out_file = alloc_printf("%s/.cur_input", out_dir); // 使用 alloc_printf 函数创建默认文件名，路径为 out_dir/.cur_input。 out_dir 应该在其它地方定义。

      /* 确保我们始终使用完全限定的 paths。 */

      if (out_file[0] == '/') aa_subst = out_file; // 如果 out_file 已经是绝对路径，则直接使用。
      else aa_subst = alloc_printf("%s/%s", cwd, out_file); // 否则，将当前工作目录和 out_file 连接起来构成绝对路径。

      /* 构造一个替换 argv 值。 */

      *aa_loc = 0; // 将 "@@" 中的第一个 '@' 替换为 '\0'，从而将字符串分割成两部分。
      n_arg = alloc_printf("%s%s%s", argv[i], aa_subst, aa_loc + 2); // 使用 alloc_printf 创建新的参数字符串，将 argv[i] 的前半部分、绝对路径 aa_subst 和 argv[i] 的后半部分连接起来。
      argv[i] = n_arg; // 将 argv[i] 指向新的参数字符串。
      *aa_loc = '@'; // 将之前被替换的 '@' 恢复。

      if (out_file[0] != '/') free(aa_subst); // 如果 out_file 不是绝对路径，则释放 aa_subst 分配的内存。

    }

    i++; // 进入下一个命令行参数。

  }

  free(cwd); /* not tracked */ // 释放 getcwd 分配的内存。

}

/* set up target path */ 
void setup_targetpath(char * argvs){
    char* cwd = getcwd(NULL, 0); // 获取当前工作目录，并将结果存储在 cwd 指针中。getcwd(NULL, 0) 会自动分配内存空间。

    target_path = alloc_printf("%s/%s", cwd, argvs); // 使用 alloc_printf 函数将当前工作目录 (cwd) 和输入参数 argvs 连接起来，形成一个绝对路径字符串。  alloc_printf 会动态分配内存来存储这个新的字符串。  结果存储在全局变量 target_path 中。

    argvs = target_path; // 将输入参数 argvs 指针指向新创建的绝对路径字符串 (target_path)。 这意味着 argvs 的值被修改了。

}

/* 对跟踪中的执行计数进行破坏性分类。这用作
   预处理步骤。召集了每一位高管，
   必须快.
   用于优化某些算法（例如模糊测试中的覆盖率统计）
   种子覆盖率的多少 */
static const u8 count_class_lookup8[256] = {

  [0]           = 0,
  [1]           = 1,
  [2]           = 2,
  [3]           = 4,
  [4 ... 7]     = 8,
  [8 ... 15]    = 16,
  [16 ... 31]   = 32,
  [32 ... 127]  = 64,
  [128 ... 255] = 128

};

static u16 count_class_lookup16[65536];


void init_count_class16(void) {

  u32 b1, b2; // 声明两个无符号32位整数变量 b1 和 b2，用于循环计数。

  for (b1 = 0; b1 < 256; b1++) // 外层循环，b1 从 0 循环到 255 (8位值的范围)。
    for (b2 = 0; b2 < 256; b2++) // 内层循环，b2 从 0 循环到 255 (8位值的范围)。
      count_class_lookup16[(b1 << 8) + b2] = // 计算 count_class_lookup16 的索引，并赋值。
        (count_class_lookup8[b1] << 8) | // 将 count_class_lookup8[b1] 左移8位，相当于乘以256。
        count_class_lookup8[b2];       // 将 count_class_lookup8[b2] 与左移后的结果进行按位或操作。

}

/*查找表将内存中某些数据分类。这个函数对传入的 mem（类型为 u64*）数组中的每个元素进行处理，
并基于 count_class_lookup16 查找表将每个元素的值转换为一个新的分类值。*/
#ifdef __x86_64__

static inline void classify_counts(u64* mem) {

  u32 i = MAP_SIZE >> 3;

  while (i--) {

    /* Optimize for sparse bitmaps. */

    if (unlikely(*mem)) {

      u16* mem16 = (u16*)mem;

      mem16[0] = count_class_lookup16[mem16[0]];
      mem16[1] = count_class_lookup16[mem16[1]];
      mem16[2] = count_class_lookup16[mem16[2]];
      mem16[3] = count_class_lookup16[mem16[3]];

    }

    mem++;

  }

}

#else
/*并优化了对稀疏位图的处理。
具体来说，它通过将每个 u32 元素拆分为两个 u16 类型的元素，
然后使用 count_class_lookup16 查找表对这两个 u16 元素进行分类*/
static inline void classify_counts(u32* mem) {

  u32 i = MAP_SIZE >> 2;

  while (i--) {

    /* 针对稀疏位图进行优化. */

    if (unlikely(*mem)) {

      u16* mem16 = (u16*)mem;

      mem16[0] = count_class_lookup16[mem16[0]];
      mem16[1] = count_class_lookup16[mem16[1]];

    }

    mem++;

  }

}

#endif /* ^__x86_64__ */


/* 通过一些简单的平滑获取可运行进程的数量。 
该函数针对不同的操作系统（macOS、FreeBSD、OpenBSD 和 Linux）使用了不同的方式来计算或估算系统的负载或可运行进程数。
函数通过加权平均的方式平滑历史值和当前值，使得系统负载的变化不会剧烈波动，避免瞬时波动对结果的影响。*/

static double get_runnable_processes(void) {

  static double res;

#if defined(__APPLE__) || defined(__FreeBSD__) || defined (__OpenBSD__)

  /* 我没有看到任何可移植的 sysctl 参数之类的，可以很快地给我们
     可运行的进程数;1 分钟平均负载可以是
     不过，半体面的近似值。 */

  if (getloadavg(&res, 1) != 1) return 0;

#else

  /* 在 Linux 上，/proc/stat 可能是最好的方法;负载平均值为
     以有趣的方式计算，有时不会反映出极其短暂的
     处理良好. */

  FILE* f = fopen("/proc/stat", "r");
  u8 tmp[1024];
  u32 val = 0;

  if (!f) return 0;

  while (fgets(tmp, sizeof(tmp), f)) {

    if (!strncmp(tmp, "procs_running ", 14) ||
        !strncmp(tmp, "procs_blocked ", 14)) val += atoi(tmp + 14);

  }
 
  fclose(f);

  if (!res) {

    res = val;

  } else {

    res = res * (1.0 - 1.0 / AVG_SMOOTHING) +
          ((double)val) * (1.0 / AVG_SMOOTHING);

  }

#endif /* ^(__APPLE__ || __FreeBSD__ || __OpenBSD__) */

  return res;

}


/* 计算逻辑 CPU 内核的数量.
获取当前系统的 CPU 核心数量，并估算当前正在运行的任务数（或负载）。
它根据操作系统的不同，采用不同的方法来获取 CPU 核心数量，
并且根据当前的任务数与 CPU 核心数量的比值，输出系统负载和性能估算 */

static void get_core_count(void) {

  u32 cur_runnable = 0;

#if defined(__APPLE__) || defined(__FreeBSD__) || defined (__OpenBSD__)

  size_t s = sizeof(cpu_core_count);

  /* 在 *BSD 系统上，我们可以使用 sysctl 来获取 CPU 的数量. */

#ifdef __APPLE__

  if (sysctlbyname("hw.logicalcpu", &cpu_core_count, &s, NULL, 0) < 0)
    return;

#else

  int s_name[2] = { CTL_HW, HW_NCPU };

  if (sysctl(s_name, 2, &cpu_core_count, &s, NULL, 0) < 0) return;

#endif /* ^__APPLE__ */

#else

#ifdef HAVE_AFFINITY

  cpu_core_count = sysconf(_SC_NPROCESSORS_ONLN);

#else

  FILE* f = fopen("/proc/stat", "r");
  u8 tmp[1024];

  if (!f) return;

  while (fgets(tmp, sizeof(tmp), f))
    if (!strncmp(tmp, "cpu", 3) && isdigit(tmp[3])) cpu_core_count++;

  fclose(f);

#endif /* ^HAVE_AFFINITY */

#endif /* ^(__APPLE__ || __FreeBSD__ || __OpenBSD__) */

  if (cpu_core_count > 0) {

    cur_runnable = (u32)get_runnable_processes();

#if defined(__APPLE__) || defined(__FreeBSD__) || defined (__OpenBSD__)

    /* 加上我们自己，因为 1 分钟平均值还不包括这个. */

    cur_runnable++;

#endif /* __APPLE__ || __FreeBSD__ || __OpenBSD__ */

    printf("You have %u CPU core%s and %u runnable tasks (utilization: %0.0f%%).\n",
        cpu_core_count, cpu_core_count > 1 ? "s" : "",
        cur_runnable, cur_runnable * 100.0 / cpu_core_count);

    if (cpu_core_count > 1) {

      if (cur_runnable > cpu_core_count * 1.5) {

        printf("System under apparent load, performance may be spotty.\n");

      }

    }

  } else {

    cpu_core_count = 0;
    printf("Unable to figure out the number of CPU cores.\n");

  }

}

/* 构建绑定到特定内核的进程列表。如果没有，则返回 -1
   可以找到。假设 4k CPU 的上限.
   将当前进程绑定到一个空闲的 CPU 核心。
   这个函数的目的是为了提高程序的性能，
   避免多个进程（特别是多任务的场景，如 AFL 运行时）同时竞争同一个 CPU 核心，
   从而通过设置 CPU 亲和性来减少 CPU 切换和上下文切换的开销。 */
static void bind_to_free_cpu(void) {

  DIR* d;
  struct dirent* de;
  cpu_set_t c;

  u8 cpu_used[4096] = { 0 };
  u32 i;

  if (cpu_core_count < 2) return;

  if (getenv("AFL_NO_AFFINITY")) {

    perror("Not binding to a CPU core (AFL_NO_AFFINITY set).");
    return;

  }

  d = opendir("/proc");

  if (!d) {

    perror("Unable to access /proc - can't scan for free CPU cores.");
    return;

  }

  printf("Checking CPU core loadout...\n");

  /* 引入一些抖动，以防多个 AFL 任务执行相同的操作
     事情。.. */

  usleep(R(1000) * 250);

  /* 扫描所有 /proc/<pid>/status 条目，检查Cpus_allowed_list。
     使用 cpu_used[] 标记绑定到特定 CPU 的所有进程。这将
     对于一些奇特的绑定设置来说是失败的，但可能几乎已经足够好了
     所有真实世界的用例。 */

  while ((de = readdir(d))) {

    u8* fn;
    FILE* f;
    u8 tmp[MAX_LINE];
    u8 has_vmsize = 0;

    if (!isdigit(de->d_name[0])) continue;

    fn = alloc_printf("/proc/%s/status", de->d_name);

    if (!(f = fopen(fn, "r"))) {
      free(fn);
      continue;
    }

    while (fgets(tmp, MAX_LINE, f)) {

      u32 hval;

      /* 没有 VmSize 的进程可能是内核任务。 */

      if (!strncmp(tmp, "VmSize:\t", 8)) has_vmsize = 1;

      if (!strncmp(tmp, "Cpus_allowed_list:\t", 19) &&
          !strchr(tmp, '-') && !strchr(tmp, ',') &&
          sscanf(tmp + 19, "%u", &hval) == 1 && hval < sizeof(cpu_used) &&
          has_vmsize) {

        cpu_used[hval] = 1;
        break;

      }

    }

    free(fn);
    fclose(f);

  }

  closedir(d);

  for (i = 0; i < cpu_core_count; i++) if (!cpu_used[i]) break;

  if (i == cpu_core_count) {
    printf("No more free CPU cores\n");

  }

  printf("Found a free CPU core, binding to #%u.\n", i);

  cpu_aff = i;

  CPU_ZERO(&c);
  CPU_SET(i, &c);

  if (sched_setaffinity(0, sizeof(c), &c))
    perror("sched_setaffinity failed\n");

}

 /* 获取 unix 时间（以微秒为单位） */
 
 static u64 get_cur_time_us(void) {
 
   struct timeval tv;
   struct timezone tz;
 
   gettimeofday(&tv, &tz);
 
   return (tv.tv_sec * 1000000ULL) + tv.tv_usec;
 
 }


/* 执行目标应用程序，监控超时。退货状态
   信息。被调用的程序将更新 trace_bits. 
   用于执行目标程序并处理超时、崩溃等异常情况的函数，
   通常用于模糊测试中与目标程序的交互。
   该函数的主要作用是在有限时间内启动目标程序（通过 fork server），
   监控其执行状态，并根据执行结果判断目标程序是否发生崩溃或超时。*/

static u8 run_target(int timeout) {

  static struct itimerval it;
  static u32 prev_timed_out = 0;

  int status = 0;

  child_timed_out = 0;

  /* 在这个 memset 之后，trace_bits[] 实际上是 volitive的，所以我们
     必须防止任何早期操作冒险进入该
     领土。 */

  memset(trace_bits, 0, MAP_SIZE);
  MEM_BARRIER();

    int res;

    /* 在非哑模式下，我们已经启动并运行了 fork 服务器，因此只需
       告诉它 have at it，然后读回 PID。 */

    if ((res = write(fsrv_ctl_fd, &prev_timed_out, 4)) != 4) {

      if (stop_soon) return 0;
      fprintf(stderr,"err%d: Unable to request new process from fork server (OOM?)", res);

    }

    if ((res = read(fsrv_st_fd, &child_pid, 4)) != 4) {

      if (stop_soon) return 0;
      fprintf(stderr, "err%d: Unable to request new process from fork server (OOM?)",res);

    }
    if (child_pid <= 0) perror("Fork server is misbehaving (OOM?)");


  /* 根据用户请求配置 timeout，然后等待 child 终止。 */

  it.it_value.tv_sec = (timeout / 1000);
  it.it_value.tv_usec = (timeout % 1000) * 1000;

  setitimer(ITIMER_REAL, &it, NULL);

  /* SIGALRM 处理程序只是杀死 child_pid 并将 child_timed_out. */



    if ((res = read(fsrv_st_fd, &status, 4)) != 4) {

      if (stop_soon) return 0;
      fprintf(stderr, "err%d: Unable to communicate with fork server (OOM?)",res);

    }


  if (!WIFSTOPPED(status)) child_pid = 0;

  it.it_value.tv_sec = 0;
  it.it_value.tv_usec = 0;

  setitimer(ITIMER_REAL, &it, NULL);

  total_execs++;

  /* trace_bits 上的任何后续操作都不得由
     编译器。经过此位置后，trace_bits[] 的行为
     非常正常，不必被视为挥发性。 */

  MEM_BARRIER();


#ifdef __x86_64__
  classify_counts((u64*)trace_bits);
#else
  classify_counts((u32*)trace_bits);
#endif /* ^__x86_64__ */

  prev_timed_out = child_timed_out;

  /* Report outcome to caller. */

  if (WIFSIGNALED(status) && !stop_soon) {

    kill_signal = WTERMSIG(status);

    if (child_timed_out && kill_signal == SIGKILL) return FAULT_TMOUT;

    return FAULT_CRASH;

  }
  return FAULT_NONE;

}

/* 将修改后的数据写入文件以进行测试。如果设置了 out_file，则旧文件
   取消链接，并创建一个新的 LINK。否则，out_fd 将倒回并
   截断.
   主要作用是将给定内存中的数据写入一个新的文件中。
   这个函数通常用于模糊测试过程中，
   将测试用例（例如某个输入数据的变异体）保存到文件中，以便后续使用或分析 */

static void write_to_testcase(void* mem, u32 len) {

  int fd = out_fd;

    unlink(out_file); /* Ignore errors. */

    fd = open(out_file, O_WRONLY | O_CREAT | O_EXCL, 0600);

    if (fd < 0) perror("Unable to create file");


  ck_write(fd, mem, len, out_file);

  close(fd);

}

/* Check CPU governor. 
检查系统中 CPU 的频率调节器（governor）设置，
并确定是否处于最优的性能模式。它会检测当前使用的 CPU governor，
如果不是性能模式（perf），则检查 CPU 的最小和最大频率，并报告是否存在不理想的配置。*/

static void check_cpu_governor(void) {

  FILE* f;
  u8 tmp[128];
  u64 min = 0, max = 0;

  if (getenv("AFL_SKIP_CPUFREQ")) return;

  f = fopen("/sys/devices/system/cpu/cpu0/cpufreq/scaling_governor", "r");
  if (!f) return;

  printf("Checking CPU scaling governor...\n");

  if (!fgets(tmp, 128, f)) perror("fgets() failed");

  fclose(f);

  if (!strncmp(tmp, "perf", 4)) return;

  f = fopen("/sys/devices/system/cpu/cpu0/cpufreq/scaling_min_freq", "r");

  if (f) {
    if (fscanf(f, "%llu", &min) != 1) min = 0;
    fclose(f);
  }

  f = fopen("/sys/devices/system/cpu/cpu0/cpufreq/scaling_max_freq", "r");

  if (f) {
    if (fscanf(f, "%llu", &max) != 1) max = 0;
    fclose(f);
  }

  if (min == max) return;

  printf("Err: Suboptimal CPU scaling governor\n");

}

/* 将一行 Gradient String 解析为 Array
将一个以逗号分隔的字符串解析成一个整数数组。 */
void parse_array(char * str, double * array){
    
    int i=0;
    
    char* token = strtok(str,",");
    
    while(token != NULL){
        array[i]=atof(token);
        i++;
        token = strtok(NULL, ",");
    }

    array[i] = 0;
}


typedef struct {
    int index;  // 存储位置（index）
    double probability;  // 存储概率值
} ProbInfo;

// 比较函数，用于按概率值排序
int compare(const void *a, const void *b) {
    ProbInfo *p1 = (ProbInfo *)a;
    ProbInfo *p2 = (ProbInfo *)b;
    if (p1->probability < p2->probability) {
        return 1;  // 返回1表示p2的概率值更大
    } else if (p1->probability > p2->probability) {
        return -1; // 返回-1表示p1的概率值更大
    }
    return 0;  // 如果相等，则返回0
}

/* 帮助程序为 fuzz_one（） 中的块操作选择随机块 len。
   如果 max_len > 0，则不返回零. 
   根据给定的限制（limit）随机选择一个块的长度。
   它会在预设的最小值和最大值之间选择一个随机长度，
   同时确保该长度不会超过提供的 limit*/

static u32 choose_block_len(u32 limit) {

  u32 min_value, max_value;

  switch ((random()%3)) {

    case 0:  min_value = 1;
             max_value = havoc_blk_small;
             break;

    case 1:  min_value = havoc_blk_small;
             max_value = havoc_blk_medium;
             break;

    case 2:  min_value = havoc_blk_medium;
             max_value = havoc_blk_large;
  }

  if (min_value >= limit) min_value = 1;

  return min_value + (random()%(MIN(max_value, limit) - min_value + 1));

}

void gen_mutate() {
    int tmout_cnt = 0;
    ProbInfo prob_info[N];
    for (int i = 0; i < N; i++) {
        prob_info[i].index = i;  // 存储位置
        prob_info[i].probability = loc[i];  // 存储概率值
    }

    // 2. 对配对数据按概率值降序排序
    qsort(prob_info, N, sizeof(ProbInfo), compare);

    // 3. 输出前10个概率最大的项
    //printf("Top probabilities:\n");
    for (int i = 0; i < N; i++) {
        //printf("Index: %d, Probability: %.7f\n", prob_info[i].index, prob_info[i].probability);
        if (prob_info[i].probability > 0.85) {
            //printf("Position: %d, Probability: %.7f\n", prob_info[i].index, prob_info[i].probability);
            bool foundNewPathOrCrash = false;  // 标志位，判断是否找到新路径或崩溃

            for (int iter = 0; iter < 13; iter++) {
                memcpy(out_buf1, out_buf, len); 
                int mut_val;
                int dex = prob_info[i].index;
                u32 random_value = random() % 256;
                mut_val = (u8)out_buf1[dex] + (u8)random_value;
                if (mut_val < 0)
                    out_buf1[dex] = 0;
                else if (mut_val > 255)
                    out_buf1[dex] = 255;
                else
                    out_buf1[dex] = mut_val;

                write_to_testcase(out_buf1, len);    

                int fault = run_target(exec_tmout); 
                if (fault != 0) {
                    if (fault == FAULT_CRASH) {
                        char* mut_fn = alloc_printf("%s/crash_%d_%06d", "./crashes", round_cnt, mut_cnt);
                        int mut_fd = open(mut_fn, O_WRONLY | O_CREAT | O_EXCL, 0600);
                        ck_write(mut_fd, out_buf1, len, mut_fn);
                        free(mut_fn);
                        close(mut_fd);
                        mut_cnt = mut_cnt + 1;

                        foundNewPathOrCrash = true;  // 标记找到崩溃
                        break;
                    }
                    else if ((fault == FAULT_TMOUT) && (tmout_cnt < 20)) {
                        tmout_cnt = tmout_cnt + 1;
                        fault = run_target(1000); 
                        if (fault == FAULT_CRASH) {
                            char* mut_fn = alloc_printf("%s/crash_%d_%06d", "./crashes", round_cnt, mut_cnt);
                            int mut_fd = open(mut_fn, O_WRONLY | O_CREAT | O_EXCL, 0600);
                            ck_write(mut_fd, out_buf1, len, mut_fn);
                            free(mut_fn);
                            close(mut_fd);
                            mut_cnt = mut_cnt + 1;

                            foundNewPathOrCrash = true;  // 标记找到崩溃
                            break;
                        } 
                    }
                }

                // 保存查找新边的 Mutations.
                int ret = has_new_bits(virgin_bits); // 检测突变是否触发了新的代码路径
                if (ret == 2) {
                    char* mut_fn = alloc_printf("%s/id_%d_%d_%06d_cov", out_dir, round_cnt, iter, mut_cnt);
                    int mut_fd = open(mut_fn, O_WRONLY | O_CREAT | O_EXCL, 0600);
                    ck_write(mut_fd, out_buf1, len, mut_fn);
                    free(mut_fn);
                    close(mut_fd);
                    mut_cnt = mut_cnt + 1;

                    foundNewPathOrCrash = true;  // 标记找到新路径
                    break;
                }
                if (ret == 1) {
                    char* mut_fn = alloc_printf("%s/id_%d_%d_%06d", out_dir, round_cnt, iter, mut_cnt);
                    int mut_fd = open(mut_fn, O_WRONLY | O_CREAT | O_EXCL, 0600);
                    ck_write(mut_fd, out_buf1, len, mut_fn);
                    free(mut_fn);
                    close(mut_fd);
                    mut_cnt = mut_cnt + 1;
                }

                // 如果此轮种子保存成功并触发新路径或崩溃，下一轮使用这个种子
                if (ret == 2 || fault == FAULT_CRASH) {
                    // 保存当前变异后的种子为下次的种子
                    memcpy(out_buf, out_buf1, len); // 重新使用保存的种子
                }
            }

            // 如果发现了新路径或者崩溃，退出当前的迭代（i 循环）继续下一个
            if (foundNewPathOrCrash) {
                continue;  // 继续处理下一个 i
            }
        }
    }
}


/* 在 dir 处干运行种子，当 stage == 1 时，将感兴趣的种子保存到 out_dir;当 stage == 2 时，计算平均执行时间 */
void dry_run(char* dir, int stage){
    DIR *dp;
    struct dirent *entry;
    struct stat statbuf;
    if((dp = opendir(dir)) == NULL) {
        fprintf(stderr,"cannot open directory: %s\n", dir);
        return;
    }
    if(chdir(dir)== -1)
        perror("chdir failed\n");
    int cnt = 0;
    u64 start_us, stop_us;
    while((entry = readdir(dp)) != NULL) { 
        if(stat(entry->d_name,&statbuf) == -1)
            continue;
        if(S_ISREG(statbuf.st_mode)) {
            char * tmp = NULL;
            tmp = strstr(entry->d_name,".");
            if(tmp != entry->d_name){
                int fd_tmp = open(entry->d_name, O_RDONLY);
                if(fd_tmp == -1)
                    perror("open failed");
                int file_len = statbuf.st_size;
                memset(out_buf1, 0, len);
                ck_read(fd_tmp, out_buf1,file_len, entry->d_name);
                
                start_us = get_cur_time_us();
                write_to_testcase(out_buf1, file_len);
                int fault = run_target(exec_tmout); 
                if (fault != 0){
                    if(fault == FAULT_CRASH){
                        char* mut_fn = alloc_printf("%s/crash_%d_%06d", "./crashes",round_cnt, mut_cnt);
                        int mut_fd = open(mut_fn, O_WRONLY | O_CREAT | O_EXCL, 0600);
                        ck_write(mut_fd, out_buf1, file_len, mut_fn);
                        free(mut_fn);
                        close(mut_fd);
                        mut_cnt = mut_cnt + 1;
                    }
                    else if(fault = FAULT_TMOUT){
                        fault = run_target(1000); 
                        if(fault == FAULT_CRASH){
                            char* mut_fn = alloc_printf("%s/crash_%d_%06d", "./crashes",round_cnt, mut_cnt);
                            int mut_fd = open(mut_fn, O_WRONLY | O_CREAT | O_EXCL, 0600);
                            ck_write(mut_fd, out_buf1, file_len, mut_fn);
                            free(mut_fn);
                            close(mut_fd);
                            mut_cnt = mut_cnt + 1;
                        } 
                    }
                }
                
                int ret = has_new_bits(virgin_bits);
                if (ret!=0){
                    if(stage == 1){
                        char* mut_fn = alloc_printf("../%s/id_%d_%06d", out_dir,round_cnt, mut_cnt);
                        int mut_fd = open(mut_fn, O_WRONLY | O_CREAT | O_EXCL, 0600);
                        ck_write(mut_fd, out_buf1, len, mut_fn);
                        free(mut_fn);
                        close(mut_fd);
                        mut_cnt = mut_cnt + 1;
                    }
                }
                
                stop_us = get_cur_time_us();
                total_cal_us = total_cal_us - start_us + stop_us;
                cnt = cnt + 1;
                close(fd_tmp);
            }
        }
    }
    if(chdir("..") == -1)
        perror("chdir failed\n");
    closedir(dp);
    
    /* 估计开始时的平均执行时间*/
    if(stage ==2 ){
        u64 avg_us = (u64)(total_cal_us / cnt);
        if (avg_us > 50000) exec_tmout = avg_us * 2 / 1000;
        else if (avg_us > 10000) exec_tmout = avg_us * 3 / 1000;
        else exec_tmout = avg_us * 5 / 1000;

        exec_tmout = (exec_tmout + 20) / 20 * 20;
        exec_tmout =  exec_tmout;
        printf("avg %d time out %d cnt %d sum %lld \n.",(int)avg_us, exec_tmout, cnt,total_cal_us);
    }

    printf("dry run %ld edge coverage %d.\n", total_execs,count_non_255_bytes(virgin_bits));
    return;
}

/*将一个文件的内容从源路径（src）复制到目标路径（dst）。
具体来说，它逐字节地读取源文件的内容，并将其写入目标文件，直到文件结束。*/
void copy_file(char* src, char* dst){
    FILE *fptr1, *fptr2;
    int c;
    fptr1 = fopen(src, "r");
    if (fptr1 == NULL)
    {
        printf("Cannot open file %s \n", src);
        exit(0);
    }

    fptr2 = fopen(dst, "w");
    if (fptr2 == NULL)
    {
        printf("Cannot open file %s \n", dst);
        exit(0);
    }

    c = fgetc(fptr1);
    while (c != EOF)
    {
        fputc(c, fptr2);
        c = fgetc(fptr1);
    }

    fclose(fptr1);
    fclose(fptr2);
    return;
}

/* 将种子从 in_idr 复制到 out_dir 
从指定的输入目录（in_dir）中读取文件，将其逐个复制到指定的输出目录（out_dir）。
每个文件的复制通过调用 copy_file 函数实现。*/
void copy_seeds(char * in_dir, char * out_dir){
    struct dirent *de; // 声明一个 dirent 结构体指针，用于存储目录项信息。
    DIR *dp; // 声明一个 DIR 指针，用于表示打开的目录流。

    if((dp = opendir(in_dir)) == NULL) { // 尝试打开 in_dir 目录。如果失败，则打印错误信息并返回。
        fprintf(stderr,"cannot open directory: %s\n", in_dir);
        return;
    }

    char src[512], dst[512]; // 声明两个字符数组，用于存储源文件路径和目标文件路径。  数组大小为 128 字节，这可能不够大，存在缓冲区溢出的风险。

    while((de = readdir(dp)) != NULL){ // 循环读取 in_dir 目录中的每个文件或目录项。readdir 函数返回一个指向 dirent 结构体的指针，该结构体包含文件或目录项的信息。

         if(strcmp(".",de->d_name) == 0 || strcmp("..",de->d_name) == 0) // 跳过 "." 和 ".." 目录项。
            continue;

        sprintf(src, "%s/%s", in_dir, de->d_name); // 构建源文件路径。
        sprintf(dst, "%s/%s", out_dir, de->d_name); // 构建目标文件路径。
        copy_file(src, dst); // 调用 copy_file 函数复制文件。  这个函数需要在其它地方定义。

    }

    closedir(dp); // 关闭打开的目录流。
    return ; // 函数返回。
}



void fuzz_lop(char * grad_file) {
    copy_file("gradient_info_p", grad_file);
    FILE *stream = fopen(grad_file, "r");
    char *line = NULL;
    size_t llen = 0;
    ssize_t nread;
    
    if (stream == NULL) {
        perror("fopen");
        exit(EXIT_FAILURE);
    }
    
    int line_cnt = 0;
    while ((nread = getline(&line, &llen, stream)) != -1) {
        line_cnt = line_cnt + 1;
        
        round_cnt++; // 轮次计数器加 1。
        now = count_non_255_bytes(virgin_bits); // 计算非 255 字节的数量。
        edge_gain = now - old; // 计算边缘增益。
        old = now; // 更新 old 值。
        
        
        char* fn = strtok(line, "|");
        char* loc_str = strtok(strtok(NULL,"|"),"\n"); ;
        
        // 输出 loc_str 以进行调试
        /*if (loc_str != NULL) {
            printf("Line %d: loc_str = %s\n", line_cnt, loc_str);
        } else {
            printf("Line %d: loc_str is NULL\n", line_cnt);
        }*/
        
        // 调用 parse_array 解析 loc_str
        //int loc[10000] = {0};  // 确保 loc 数组初始化为 0
        parse_array(loc_str, loc);

        // 输出 loc 数组，检查是否正确填充
        /*printf("Line %d: LOC array = ", line_cnt);
        for (int i = 0; loc[i] != 0; i++) {  // 假设 loc 数组初始化为 0
            printf("%f ", loc[i]);
        }
        printf("\n");
        
        // 打印种子路径
        printf("Seed path: %s\n", fn);*/
        
        
                /* 每 10 个文件的打印边缘覆盖率*/
        if((line_cnt % 10) == 0){ // 每 10 行打印一次边缘覆盖率信息。
            printf("$$$$&&&& fuzz %s line_cnt %d\n",fn, line_cnt); // 打印文件名和行号。
            printf("edge num %d\n",count_non_255_bytes(virgin_bits)); // 打印边缘覆盖率。
            fflush(stdout); // 刷新输出缓冲区。
        }
        
        
        
        int fn_fd = open(fn, O_RDONLY);
        if (fn_fd == -1) {
            perror("open failed");
            exit(0);
        }
        struct stat st;
        int ret = fstat(fn_fd,&st); // 获取文件状态。
        int file_len = st.st_size; // 获取文件大小。
        memset(out_buf1,0,len); // 清零缓冲区。
        memset(out_buf2,0,len);
        memset(out_buf,0, len); // 清零缓冲区。
        memset(out_buf3,0, 20000); // 清零缓冲区。
        ck_read(fn_fd, out_buf, file_len, fn); // 读取种子文件到缓冲区。
        gen_mutate();
    }
    
    free(line);
    fclose(stream);
}
/* 连接到 python NN 模块，然后读取梯度文件以指导模糊测试 
在模糊测试过程中结合梯度信息、网络交互和文件操作来进行输入突变优化。
void start_fuzz(int f_len){

    连接到 Python 模块  
    struct sockaddr_in address; // 定义一个 sockaddr_in 结构体，用于存储服务器地址信息。
    int sock = 0; // 定义一个整数变量，用于存储套接字描述符。
    struct sockaddr_in serv_addr; // 定义一个 sockaddr_in 结构体，用于存储服务器地址信息。
    if ((sock = socket(AF_INET, SOCK_STREAM, 0)) < 0){ // 创建一个 IPv4 TCP 套接字。
        perror("Socket creation error"); // 如果创建套接字失败，则打印错误信息。
        exit(0); // 退出程序。
    }
    memset(&serv_addr, '0', sizeof(serv_addr)); // 将 serv_addr 结构体清零。
    serv_addr.sin_family = AF_INET; // 设置地址族为 IPv4。
    serv_addr.sin_port = htons(PORT); // 设置端口号，PORT 应该在其他地方定义。 htons 将主机字节序转换为网络字节序。
    if(inet_pton(AF_INET, "127.0.0.1", &serv_addr.sin_addr)<=0){ // 将 IP 地址 "127.0.0.1" 转换为网络字节序，并存储到 serv_addr.sin_addr 中。
        perror("Invalid address/ Address not supported"); // 如果转换失败，则打印错误信息。
        exit(0); // 退出程序。
    }
    if (connect(sock, (struct sockaddr *)&serv_addr, sizeof(serv_addr)) < 0){ // 连接到服务器。
        perror("Connection Failed"); // 如果连接失败，则打印错误信息。
        exit(0); // 退出程序。
    }

     设置 buffer 
    out_buf = malloc(10000); // 分配 10000 字节的内存给 out_buf。
    if(!out_buf)
        perror("malloc failed"); // 如果内存分配失败，则打印错误信息。
    out_buf1 = malloc(10000); // 分配 10000 字节的内存给 out_buf1。
    if(!out_buf1)
        perror("malloc failed");
    out_buf2 = malloc(10000); // 分配 10000 字节的内存给 out_buf2。
    if(!out_buf2)
        perror("malloc failed");
    out_buf3 = malloc(20000); // 分配 20000 字节的内存给 out_buf3。
    if(!out_buf3)
        perror("malloc failed");

    len = f_len; // 将 f_len 赋值给 len。

     dry run seeds
    dry_run(out_dir, 2); // 执行 dry_run 函数，参数为 out_dir 和 2。 dry_run 函数应该在其他地方定义。

     start fuzz 
    char buf[16]; // 定义一个字符数组，用于接收数据。
    while(1){ // 无限循环，开始模糊测试。
        if(read(sock , buf, 5)== -1) // 从套接字读取 5 个字节的数据。
            perror("received failed\n"); // 如果读取失败，则打印错误信息。
        fuzz_lop("gradient_info", sock); // 调用 fuzz_lop 函数，参数为 "gradient_info" 和 sock。 fuzz_lop 函数应该在其他地方定义。
        printf("receive\n"); // 打印信息。
    }
    return;
}

 函数进行本地调试，请替换为 start_fuzz 
用于在测试环境下执行一次初始化操作和模糊测试循环，
主要目的是验证模糊测试核心逻辑的正确性，而无需与外部 Python 模块进行通信。*/
void start_fuzz_test(int f_len){
    int sock = 0;
    
    /* set up buffer */
    out_buf = malloc(10000);
    if(!out_buf)
        perror("malloc failed");
    out_buf1 = malloc(10000);
    if(!out_buf1)
        perror("malloc failed");
    out_buf2 = malloc(10000);
    if(!out_buf2)
        perror("malloc failed");
    out_buf3 = malloc(20000);
    if(!out_buf3)
        perror("malloc failed");
    
    len = f_len;
    /* dry run */
    dry_run(out_dir, 0);
    /* fuzz */
        fuzz_lop("gradient_info");
    return;
}


void main(int argc, char*argv[]){
    int opt;
while ((opt = getopt(argc, argv, "+i:o:l:")) > 0) // 使用 getopt 解析命令行参数。"+i:o:l:" 指定支持 -i, -o, -l 选项，并且每个选项都接受一个参数。  '+' 表示忽略任何未知选项。
    switch (opt) { // 根据 getopt 返回的选项进行处理。
      case 'i': /* input dir */ // 处理 -i 选项 (输入目录)。
        if (in_dir) perror("Multiple -i options not supported"); // 检查是否已经设置了 in_dir，如果已经设置则报错。
        in_dir = optarg; // 将 optarg (选项参数) 赋值给 in_dir。
        break;

      case 'o': /* output dir */ // 处理 -o 选项 (输出目录)。
        if (out_dir) perror("Multiple -o options not supported"); // 检查是否已经设置了 out_dir，如果已经设置则报错。
        out_dir = optarg; // 将 optarg 赋值给 out_dir。
        break;

      case 'l': /* file len */ // 处理 -l 选项 (文件长度)。
         sscanf (optarg,"%ld",&len); // 将 optarg 转换为长整数，并赋值给 len。
         /* 根据文件 len 更改 num_index 和 havoc_blk_* */
         if(len > 7000) // 根据文件长度设置不同的值。
         {
             num_index[13] = (len - 1);
             havoc_blk_large = (len - 1);
         }
         else if (len > 4000)
         {
             num_index[13] = (len - 1);
             num_index[12] = 3072;
             havoc_blk_large = (len - 1);
             havoc_blk_medium = 2048; 
             havoc_blk_small = 1024;
         }
         printf("num_index %d %d small %d medium %d large %d\n", num_index[12], num_index[13], havoc_blk_small, havoc_blk_medium, havoc_blk_large); // 打印 num_index 和 havoc_blk_* 的值。
         printf("mutation len: %ld\n", len); // 打印文件长度。
         break;

      default: // 处理未知选项。
        printf("no manual..."); // 打印提示信息。
    }
    
    setup_signal_handlers();
    check_cpu_governor();
    get_core_count();
    bind_to_free_cpu();
    setup_shm();
    init_count_class16();
    setup_dirs_fds();
    if (!out_file) setup_stdio_file();
    detect_file_args(argv + optind + 1);
    setup_targetpath(argv[optind]);
    
    copy_seeds(in_dir, out_dir);
    init_forkserver(argv+optind);
   
    start_fuzz_test(len);   
    printf("total execs %ld edge coverage %d.\n", total_execs, count_non_255_bytes(virgin_bits));
    return;
}

