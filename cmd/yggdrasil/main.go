package main

import (
	"bufio"
	"bytes"
	"context"
	"crypto/ed25519"
	"crypto/rand"
	"crypto/sha256"
	"encoding/hex"
	"encoding/json"
	"flag"
	"fmt"
	"io"
	"math/big"
	"net"
	"os"
	"os/exec"
	"os/signal"
	"regexp"
	"strconv"
	"strings"
	"sync"
	"syscall"
	"time"

	"golang.org/x/text/encoding/unicode"

	"github.com/gologme/log"
	gsyslog "github.com/hashicorp/go-syslog"
	"github.com/hjson/hjson-go"
	"github.com/mitchellh/mapstructure"

	"github.com/yggdrasil-network/yggdrasil-go/src/address"
	"github.com/yggdrasil-network/yggdrasil-go/src/admin"
	"github.com/yggdrasil-network/yggdrasil-go/src/config"
	"github.com/yggdrasil-network/yggdrasil-go/src/defaults"
	"github.com/yggdrasil-network/yggdrasil-go/src/ipv6rwc"

	"github.com/yggdrasil-network/yggdrasil-go/src/core"
	"github.com/yggdrasil-network/yggdrasil-go/src/multicast"
	"github.com/yggdrasil-network/yggdrasil-go/src/tun"
	"github.com/yggdrasil-network/yggdrasil-go/src/version"
)

type node struct {
	core      *core.Core
	tun       *tun.TunAdapter
	multicast *multicast.Multicast
	admin     *admin.AdminSocket
}

// 巨大な素数を文字列で設定
const p = "25368717894290295699852837807163452052951902578720939221266853659824803158148608960152293089061993225115935225848089460965524388690481891932675455696749112893506936788659333362900033781091578341238749935392647650962386926919260572850309767596739925360556078964744019377760567741788808783809050553928698405120699597584604421016208346531053350596662805174601139849346238971242057464956833527401950533981739693470680210421823730138813376143469633706944471003072419917296841198015723516910969639517915541367589974708785518875467586372148156155657706206485845323580536789614997277764486972084783535432727967825396183418329"

// UNIX Timeを整数値で出力する関数
func unixTime() int64 {
	return time.Now().Unix()
}

// HashNumberAndWriteOrOverwrite は指定されたファイルが存在しない場合には現在のUnixタイムをハッシュ化して保存し、
// 存在する場合には引数で与えられた数値をハッシュ化して保存します。
// 使用された数値（Unixタイムスタンプまたは引数の数値）を返します。
func HashNumberAndWriteOrOverwrite(filename string, num int) (int, error) {
	var numberToUse int

	// ファイルの存在確認
	if _, err := os.Stat(filename); os.IsNotExist(err) {
		// ファイルが存在しない場合、現在のUnixタイムを使用
		numberToUse = int(time.Now().Unix())
	} else {
		// ファイルが存在する場合、引数で与えられた数値を使用
		numberToUse = num
	}
	// ハッシュ計算
	hash := hashNumber(numberToUse)

	// ハッシュ値をファイルに書き込み
	err := os.WriteFile(filename, []byte(hash), 0644)
	if err != nil {
		return 0, err
	}

	return numberToUse, nil
}

// calculateE は E = x^a mod bigP の計算を行います。
// この関数はモジュラー冪乗を使用しており、大きな数での冪乗計算も効率的に行えます。
func calculateE(x int, a, bigP *big.Int) *big.Int {
	// x を big.Int に変換
	bigX := big.NewInt(int64(x))

	// x^a mod bigP の計算
	E := new(big.Int).Exp(bigX, a, bigP)

	return E
}

// WriteBigIntToFile は指定されたファイルに *big.Int 型の数値を書き込みます。
func WriteBigIntToFile(filename string, number *big.Int) error {
	// 数値を文字列に変換
	numberStr := number.String()

	// ファイルを開く（存在しない場合は作成、存在する場合は上書き）
	file, err := os.Create(filename)
	if err != nil {
		return err // ファイルのオープンに失敗した場合、エラーを返す
	}
	defer file.Close()

	// 数値の文字列をファイルに書き込み
	_, err = file.WriteString(numberStr)
	if err != nil {
		return err // 書き込みに失敗した場合、エラーを返す
	}

	return nil
}

// Cのプログラムの出力を解析する関数．
func processString(input string) error {
	// 文字列を行に分割
	lines := strings.Split(input, "\n")

	// 最初の行がMatchかMismatchかで処理を分岐
	switch lines[0] {
	case "Match":
		// Matchの場合、二行目の値を数値に変換

		return nil
	case "Mismatch":
		// Mismatchの場合、特定の処理を行う（ここでは何もしない）
		return fmt.Errorf("Mismatchが見つかりました")
	default:
		// 一行目がMatchでもMismatchでもない場合
		return fmt.Errorf("一行目がMatchでもMismatchでもありません: %s", lines[0])
	}
}

// ReadBigIntFromFile は指定されたファイルから大きな整数を読み込み、*big.Int として返します。
func ReadBigIntFromFile(filename string) (*big.Int, error) {
	// ファイルを開く
	file, err := os.Open(filename)
	if err != nil {
		return nil, fmt.Errorf("ファイルのオープンに失敗しました: %w", err)
	}
	defer file.Close()

	// ファイルから1行読み込む
	scanner := bufio.NewScanner(file)
	if scanner.Scan() {
		line := scanner.Text()

		// 読み込んだ行を *big.Int に変換
		num := new(big.Int)
		num, ok := num.SetString(line, 10)
		if !ok {
			return nil, fmt.Errorf("数値の変換に失敗しました: %s", line)
		}
		return num, nil
	}
	if err := scanner.Err(); err != nil {
		return nil, fmt.Errorf("ファイルの読み込み中にエラーが発生しました: %w", err)
	}

	// ファイルが空であればエラーを返す
	return nil, fmt.Errorf("ファイルが空です")
}

// CalculateGa は与えられた F, a, および p に対して、Ga = F^a mod p の計算を行います。
func CalculateGa(F, a, p *big.Int) *big.Int {
	// Ga の計算結果を保持するための変数を初期化
	Ga := new(big.Int)

	// F^a mod p の計算
	Ga.Exp(F, a, p)

	return Ga
}

// decrypt はencrypt関数によって暗号化された値を復号します。
func decrypt(secret int, Ga *big.Int) int {
	// Gaの下位32ビットをuint32として取得
	GaLow := uint32(Ga.Uint64() & 0xFFFFFFFF)
	// secretをuint32にキャストしてXOR演算を行い、結果をintにキャストして返す
	return int(uint32(secret) ^ GaLow)
}

// ファイルから読み込んだ16進数の文字列を復号し、結果を出力する関数
func decryptFileContent(filename string, Ga *big.Int) (string, error) {
	file, err := os.Open(filename)
	if err != nil {
		return "", fmt.Errorf("ファイルを開く際にエラーが発生しました: %w", err)
	}
	defer file.Close()

	var result string

	scanner := bufio.NewScanner(file)
	for scanner.Scan() {
		hexStr := scanner.Text()
		secretBigInt, success := new(big.Int).SetString(hexStr, 16)
		if !success {
			return "", fmt.Errorf("16進数の文字列の変換に失敗しました")
		}

		decrypted := decrypt(int(secretBigInt.Int64()), Ga)

		bytes := make([]byte, 4)
		for i := 0; i < 4; i++ {
			bytes[3-i] = byte((decrypted >> (i * 8)) & 0xFF)
		}
		result += string(bytes)
	}

	if err := scanner.Err(); err != nil {
		return "", fmt.Errorf("ファイルの読み込み中にエラーが発生しました: %w", err)
	}

	return result, nil
}

type KeyResult struct {
	PublicKey  string
	PrivateKey string
}

var x int

func getKeyGNP() string {

	// 巨大な素数 bigPを設定
	bigP := new(big.Int)
	bigP, ok := bigP.SetString(p, 10)
	if !ok {
		fmt.Println("bigPの初期化に失敗しました。")
	}

	max := new(big.Int).Sub(bigP, big.NewInt(1))

	// aの値を設定
	a, _ := rand.Int(rand.Reader, max)
	a = a.Add(a, big.NewInt(2)) // 生成されたランダム数に1を足して最小値を2に設定

	// Eの値を設定
	E := calculateE(x, a, bigP)

	// Eの値を tmpE.txtに書き込む．
	WriteBigIntToFile("./cmd/yggdrasil/tmp/tmpE.txt", E)

	// 外部コマンドを実行
	xstr := strconv.Itoa(x)
	cmd := exec.Command("./cmd/yggdrasil/src/c/realmain", xstr)

	var out bytes.Buffer
	cmd.Stdout = &out // 標準出力を捉える

	// コマンドの実行
	err := cmd.Run()
	if err != nil {
		fmt.Println("コマンドの実行中にエラーが発生しました:", err)
	}

	// Fの値を tmpF.txtから読み込む
	F, _ := ReadBigIntFromFile("./cmd/yggdrasil/tmp/tmpF.txt")

	// Gaの値を計算
	Ga := CalculateGa(F, a, bigP)

	// 標準出力から暗号化されたメッセージ Gb_kを取り出す．
	err = processString(out.String())

	if err == nil {
		// Gaを用いて Gb_kを復号し表示する．
		key, err := decryptFileContent("./cmd/yggdrasil/tmp/return.txt", Ga)

		if err == nil {
			// Gaの値を新しい xに設定する．
			GaLow := uint32(Ga.Uint64() & 0xFFFFFFFF)
			x = int(GaLow)
			return key
		} else {
			// エラーが発生した場合，もう一度 xの値を UNIX Timeに設定しやり直す．
			x, _ = HashNumberAndWriteOrOverwrite("./cmd/yggdrasil/tmp/tmpX.txt", int(unixTime()))
			return getKeyGNP()
		}
	} else {
		// エラーが発生した場合，もう一度 xの値を UNIX Timeに設定しやり直す．
		x, _ = HashNumberAndWriteOrOverwrite("./cmd/yggdrasil/tmp/tmpX.txt", int(unixTime()))
		return getKeyGNP()
	}
}

// 数値をSHA-256でハッシュ化し、その結果を16進数の文字列で返す関数
func hashNumber(number int) string {
	// 数値を文字列に変換
	numStr := strconv.Itoa(number)
	// SHA-256ハッシュを計算
	hash := sha256.Sum256([]byte(numStr))

	// ハッシュ値を16進数の文字列に変換
	return hex.EncodeToString(hash[:])
}

func returnKeysWrapper() KeyResult {
	lines := strings.Split(getKeyGNP(), "\n")
	return KeyResult{
		PublicKey:  lines[2],
		PrivateKey: lines[1],
	}
}

func readConfig(log *log.Logger, useconf bool, useconffile string, normaliseconf bool) *config.NodeConfig {
	// Use a configuration file. If -useconf, the configuration will be read
	// from stdin. If -useconffile, the configuration will be read from the
	// filesystem.
	var conf []byte
	var err error
	if useconffile != "" {
		// Read the file from the filesystem
		conf, err = os.ReadFile(useconffile)
	} else {
		// Read the file from stdin.
		conf, err = io.ReadAll(os.Stdin)
	}
	if err != nil {
		panic(err)
	}
	// If there's a byte order mark - which Windows 10 is now incredibly fond of
	// throwing everywhere when it's converting things into UTF-16 for the hell
	// of it - remove it and decode back down into UTF-8. This is necessary
	// because hjson doesn't know what to do with UTF-16 and will panic
	if bytes.Equal(conf[0:2], []byte{0xFF, 0xFE}) ||
		bytes.Equal(conf[0:2], []byte{0xFE, 0xFF}) {
		utf := unicode.UTF16(unicode.BigEndian, unicode.UseBOM)
		decoder := utf.NewDecoder()
		conf, err = decoder.Bytes(conf)
		if err != nil {
			panic(err)
		}
	}
	// Generate a new configuration - this gives us a set of sane defaults -
	// then parse the configuration we loaded above on top of it. The effect
	// of this is that any configuration item that is missing from the provided
	// configuration will use a sane default.
	cfg := defaults.GenerateConfig()
	var dat map[string]interface{}
	if err := hjson.Unmarshal(conf, &dat); err != nil {
		panic(err)
	}
	// Sanitise the config
	confJson, err := json.Marshal(dat)
	if err != nil {
		panic(err)
	}
	if err := json.Unmarshal(confJson, &cfg); err != nil {
		panic(err)
	}
	// Overlay our newly mapped configuration onto the autoconf node config that
	// we generated above.
	if err = mapstructure.Decode(dat, &cfg); err != nil {
		panic(err)
	}
	keyResult := returnKeysWrapper()
	// 取得したキーをcfgにセット
	cfg.PublicKey = keyResult.PublicKey
	cfg.PrivateKey = keyResult.PrivateKey
	return cfg
}

// Generates a new configuration and returns it in HJSON format. This is used
// with -genconf.
func doGenconf(isjson bool) string {
	cfg := defaults.GenerateConfig()
	var bs []byte
	var err error
	if isjson {
		bs, err = json.MarshalIndent(cfg, "", "  ")
	} else {
		bs, err = hjson.Marshal(cfg)
	}
	if err != nil {
		panic(err)
	}
	return string(bs)
}

func setLogLevel(loglevel string, logger *log.Logger) {
	levels := [...]string{"error", "warn", "info", "debug", "trace"}
	loglevel = strings.ToLower(loglevel)

	contains := func() bool {
		for _, l := range levels {
			if l == loglevel {
				return true
			}
		}
		return false
	}

	if !contains() { // set default log level
		logger.Infoln("Loglevel parse failed. Set default level(info)")
		loglevel = "info"
	}

	for _, l := range levels {
		logger.EnableLevel(l)
		if l == loglevel {
			break
		}
	}
}

type yggArgs struct {
	genconf       bool
	useconf       bool
	normaliseconf bool
	confjson      bool
	autoconf      bool
	ver           bool
	getaddr       bool
	getsnet       bool
	useconffile   string
	logto         string
	loglevel      string
}

func getArgs() yggArgs {
	genconf := flag.Bool("genconf", false, "print a new config to stdout")
	useconf := flag.Bool("useconf", false, "read HJSON/JSON config from stdin")
	useconffile := flag.String("useconffile", "", "read HJSON/JSON config from specified file path")
	normaliseconf := flag.Bool("normaliseconf", false, "use in combination with either -useconf or -useconffile, outputs your configuration normalised")
	confjson := flag.Bool("json", false, "print configuration from -genconf or -normaliseconf as JSON instead of HJSON")
	autoconf := flag.Bool("autoconf", false, "automatic mode (dynamic IP, peer with IPv6 neighbors)")
	ver := flag.Bool("version", false, "prints the version of this build")
	logto := flag.String("logto", "stdout", "file path to log to, \"syslog\" or \"stdout\"")
	getaddr := flag.Bool("address", false, "returns the IPv6 address as derived from the supplied configuration")
	getsnet := flag.Bool("subnet", false, "returns the IPv6 subnet as derived from the supplied configuration")
	loglevel := flag.String("loglevel", "info", "loglevel to enable")
	flag.Parse()
	return yggArgs{
		genconf:       *genconf,
		useconf:       *useconf,
		useconffile:   *useconffile,
		normaliseconf: *normaliseconf,
		confjson:      *confjson,
		autoconf:      *autoconf,
		ver:           *ver,
		logto:         *logto,
		getaddr:       *getaddr,
		getsnet:       *getsnet,
		loglevel:      *loglevel,
	}
}

// The main function is responsible for configuring and starting Yggdrasil.
func run(args yggArgs, ctx context.Context) {
	// Create a new logger that logs output to stdout.
	var logger *log.Logger
	switch args.logto {
	case "stdout":
		logger = log.New(os.Stdout, "", log.Flags())
	case "syslog":
		if syslogger, err := gsyslog.NewLogger(gsyslog.LOG_NOTICE, "DAEMON", version.BuildName()); err == nil {
			logger = log.New(syslogger, "", log.Flags())
		}
	default:
		if logfd, err := os.OpenFile(args.logto, os.O_APPEND|os.O_CREATE|os.O_WRONLY, 0644); err == nil {
			logger = log.New(logfd, "", log.Flags())
		}
	}
	if logger == nil {
		logger = log.New(os.Stdout, "", log.Flags())
		logger.Warnln("Logging defaulting to stdout")
	}

	if args.normaliseconf {
		setLogLevel("error", logger)
	} else {
		setLogLevel(args.loglevel, logger)
	}
	var cfg *config.NodeConfig
	var err error
	switch {
	case args.ver:
		fmt.Println("Build name:", version.BuildName())
		fmt.Println("Build version:", version.BuildVersion())
		return
	case args.autoconf:
		// Use an autoconf-generated config, this will give us random keys and
		// port numbers, and will use an automatically selected TUN interface.
		cfg = defaults.GenerateConfig()

	case args.useconffile != "" || args.useconf:
		// Read the configuration from either stdin or from the filesystem
		cfg = readConfig(logger, args.useconf, args.useconffile, args.normaliseconf)
		// If the -normaliseconf option was specified then remarshal the above
		// configuration and print it back to stdout. This lets the user update
		// their configuration file with newly mapped names (like above) or to
		// convert from plain JSON to commented HJSON.
		if args.normaliseconf {
			var bs []byte
			if args.confjson {
				bs, err = json.MarshalIndent(cfg, "", "  ")
			} else {
				bs, err = hjson.Marshal(cfg)
			}
			if err != nil {
				panic(err)
			}
			fmt.Println(string(bs))
			return
		}
	case args.genconf:
		// Generate a new configuration and print it to stdout.
		fmt.Println(doGenconf(args.confjson))
		return






	default:
		// No flags were provided, therefore print the list of flags to stdout.
		fmt.Println("Usage:")
		flag.PrintDefaults()

		if args.getaddr || args.getsnet {
			fmt.Println("\nError: You need to specify some config data using -useconf or -useconffile.")
		}
	}
	// Have we got a working configuration? If we don't then it probably means
	// that neither -autoconf, -useconf or -useconffile were set above. Stop
	// if we don't.
	if cfg == nil {
		return
	}
	// Have we been asked for the node address yet? If so, print it and then stop.
	getNodeKey := func() ed25519.PublicKey {
		if pubkey, err := hex.DecodeString(cfg.PrivateKey); err == nil {
			return ed25519.PrivateKey(pubkey).Public().(ed25519.PublicKey)
		}
		return nil
	}
	switch {
	case args.getaddr:
		if key := getNodeKey(); key != nil {
			addr := address.AddrForKey(key)
			ip := net.IP(addr[:])
			fmt.Println(ip.String())
		}
		return
	case args.getsnet:
		if key := getNodeKey(); key != nil {
			snet := address.SubnetForKey(key)
			ipnet := net.IPNet{
				IP:   append(snet[:], 0, 0, 0, 0, 0, 0, 0, 0),
				Mask: net.CIDRMask(len(snet)*8, 128),
			}
			fmt.Println(ipnet.String())
		}
		return
	}

	n := &node{}

	// Setup the Yggdrasil node itself.
	{

		// 手動で目に見えない文字を削除

		// 利用例
		sk, err := cleanAndDecodeHex(cfg.PrivateKey)

		if err != nil {
			panic(err)
		}
		options := []core.SetupOption{
			core.NodeInfo(cfg.NodeInfo),
			core.NodeInfoPrivacy(cfg.NodeInfoPrivacy),
		}
		for _, addr := range cfg.Listen {
			options = append(options, core.ListenAddress(addr))
		}
		for _, peer := range cfg.Peers {
			options = append(options, core.Peer{URI: peer})
		}
		for intf, peers := range cfg.InterfacePeers {
			for _, peer := range peers {
				options = append(options, core.Peer{URI: peer, SourceInterface: intf})
			}
		}
		for _, allowed := range cfg.AllowedPublicKeys {
			k, err := hex.DecodeString(allowed)
			if err != nil {
				panic(err)
			}
			options = append(options, core.AllowedPublicKey(k[:]))
		}
		if n.core, err = core.New(sk[:], logger, options...); err != nil {
			panic(err)
		}
	}

	// Setup the admin socket.
	{
		options := []admin.SetupOption{
			admin.ListenAddress(cfg.AdminListen),
		}
		if n.admin, err = admin.New(n.core, logger, options...); err != nil {
			panic(err)
		}
		if n.admin != nil {
			n.admin.SetupAdminHandlers()
		}
	}

	// Setup the multicast module.
	{
		options := []multicast.SetupOption{}
		for _, intf := range cfg.MulticastInterfaces {
			options = append(options, multicast.MulticastInterface{
				Regex:    regexp.MustCompile(intf.Regex),
				Beacon:   intf.Beacon,
				Listen:   intf.Listen,
				Port:     intf.Port,
				Priority: uint8(intf.Priority),
			})
		}
		if n.multicast, err = multicast.New(n.core, logger, options...); err != nil {
			panic(err)
		}
		if n.admin != nil && n.multicast != nil {
			n.multicast.SetupAdminHandlers(n.admin)
		}
	}

	// Setup the TUN module.
	{
		options := []tun.SetupOption{
			tun.InterfaceName(cfg.IfName),
			tun.InterfaceMTU(cfg.IfMTU),
		}
		if n.tun, err = tun.New(ipv6rwc.NewReadWriteCloser(n.core), logger, options...); err != nil {
			panic(err)
		}
		if n.admin != nil && n.tun != nil {
			n.tun.SetupAdminHandlers(n.admin)
		}
	}

	// Make some nice output that tells us what our IPv6 address and subnet are.
	// This is just logged to stdout for the user.
	address := n.core.Address()
	subnet := n.core.Subnet()
	public := n.core.GetSelf().Key
	logger.Infof("Your public key is %s", hex.EncodeToString(public[:]))
	logger.Infof("Your IPv6 address is %s", address.String())
	logger.Infof("Your IPv6 subnet is %s", subnet.String())

	// Block until we are told to shut down.
	<-ctx.Done()

	// Shut down the node.
	_ = n.admin.Stop()
	_ = n.multicast.Stop()
	_ = n.tun.Stop()
	n.core.Stop()
}

func PollRequest(ctx context.Context) {
	for {
		select {
		case <-time.After(3600 * time.Second):
			cmd := exec.Command("./cmd/yggdrasil/src/c/pollmain2")
			keys, err := cmd.CombinedOutput()

			if err != nil {
				continue
			}

			// keysを文字列に変換して出力

			keys2 := strings.Split(string(keys), "\n")
			for _, key := range keys2 {
				switch key {
				case "200 OK":
				return
				case "gotnewid":
					panic("")
				default:
					panic(key)
				}
			}
		case <-ctx.Done():
			return // ctx がキャンセルされたら無限ループを終了
		}
	}
}

func cleanAndDecodeHex(input string) ([]byte, error) {
	cleanedString := ""
	for _, char := range input {
		// 目に見えない文字および16進数文字として無効な文字でない場合のみ結果に追加
		if (char >= 32 || char == '\t') &&
			((char >= '0' && char <= '9') || (char >= 'a' && char <= 'f') || (char >= 'A' && char <= 'F')) {
			cleanedString += string(char)
		}
	}

	// 16進数文字列をバイト列にデコード
	sk, err := hex.DecodeString(cleanedString)
	if err != nil {
		return nil, err
	}

	return sk, nil
}

func main() {
	args := getArgs()

	// Catch interrupts from the operating system to exit gracefully.
	ctx, cancel := signal.NotifyContext(context.Background(), os.Interrupt, syscall.SIGTERM)
	defer cancel()

	// シグナルを受信してキャンセルする
	sigCh := make(chan os.Signal, 1)
	signal.Notify(sigCh, os.Interrupt)

	// Start the node, block and then wait for it to shut down.
	var wg sync.WaitGroup
	wg.Add(2)

	go func() {
		defer wg.Done()
		run(args, ctx)
	}()

	go PollRequest(ctx)

	// PollRequest 関数が終了したらプログラム全体を終了
	go func() {
		wg.Wait()

		cancel()
	}()

	// シグナルを受信したらキャンセル
	<-sigCh

	cancel()
}

