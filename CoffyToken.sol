// SPDX-License-Identifier: MIT

pragma solidity 0.8.25;

/*
    ..######...#######..########.########.####
    .##....##.##.....##.##.......##........##.
    .##.......##.....##.##.......##........##.
    .##.......##.....##.######...######....##.
    .##.......##.....##.##.......##........##.
    .##....##.##.....##.##.......##........##.
    ..######...#######..##.......##.......####

    The Unified DAPP for Simplified DeFi.

    Website:            https://coffy.io
    Twitter:            https://x.com/CoffyDeFi
    TG Announcements:   https://t.me/CoffyRelay
    TG Community:       https://t.me/CoffyPortal

    Maximize Your DeFi Earnings with CoffyDeFi.
*/

interface IERC20 {
    function totalSupply() external view returns (uint256);
    
    function balanceOf(address account) external view returns (uint256);
    
    function transfer(
        address recipient,
        uint256 amount
    ) external returns (bool);
    
    function allowance(
        address owner,
        address spender
    ) external view returns (uint256);

    function approve(address spender, uint256 amount) external returns (bool);

    function transferFrom(
        address sender,
        address recipient,
        uint256 amount
    ) external returns (bool);

    event Transfer(address indexed from, address indexed to, uint256 value);

    event Approval(
        address indexed owner,
        address indexed spender,
        uint256 value
    );
}

interface IERC20Metadata is IERC20 {
    function name() external view returns (string memory);

    function symbol() external view returns (string memory);

    function decimals() external view returns (uint8);
}

library Address {
    function isContract(address account) internal view returns (bool) {
        return account.code.length > 0;
    }

    function sendValue(address payable recipient, uint256 amount) internal {
        require(
            address(this).balance >= amount,
            "Address: insufficient balance"
        );

        (bool success, ) = recipient.call{value: amount}("");
        require(
            success,
            "Address: unable to send value, recipient may have reverted"
        );
    }

    function functionCall(
        address target,
        bytes memory data
    ) internal returns (bytes memory) {
        return functionCall(target, data, "Address: low-level call failed");
    }

    function functionCall(
        address target,
        bytes memory data,
        string memory errorMessage
    ) internal returns (bytes memory) {
        return functionCallWithValue(target, data, 0, errorMessage);
    }

    function functionCallWithValue(
        address target,
        bytes memory data,
        uint256 value
    ) internal returns (bytes memory) {
        return
            functionCallWithValue(
                target,
                data,
                value,
                "Address: low-level call with value failed"
            );
    }

    function functionCallWithValue(
        address target,
        bytes memory data,
        uint256 value,
        string memory errorMessage
    ) internal returns (bytes memory) {
        require(
            address(this).balance >= value,
            "Address: insufficient balance for call"
        );
        require(isContract(target), "Address: call to non-contract");

        (bool success, bytes memory returndata) = target.call{value: value}(
            data
        );
        return verifyCallResult(success, returndata, errorMessage);
    }

    function functionStaticCall(
        address target,
        bytes memory data
    ) internal view returns (bytes memory) {
        return
            functionStaticCall(
                target,
                data,
                "Address: low-level static call failed"
            );
    }

    function functionStaticCall(
        address target,
        bytes memory data,
        string memory errorMessage
    ) internal view returns (bytes memory) {
        require(isContract(target), "Address: static call to non-contract");

        (bool success, bytes memory returndata) = target.staticcall(data);
        return verifyCallResult(success, returndata, errorMessage);
    }

    function functionDelegateCall(
        address target,
        bytes memory data
    ) internal returns (bytes memory) {
        return
            functionDelegateCall(
                target,
                data,
                "Address: low-level delegate call failed"
            );
    }

    function functionDelegateCall(
        address target,
        bytes memory data,
        string memory errorMessage
    ) internal returns (bytes memory) {
        require(isContract(target), "Address: delegate call to non-contract");

        (bool success, bytes memory returndata) = target.delegatecall(data);
        return verifyCallResult(success, returndata, errorMessage);
    }

    function verifyCallResult(
        bool success,
        bytes memory returndata,
        string memory errorMessage
    ) internal pure returns (bytes memory) {
        if (success) {
            return returndata;
        } else {
            // Look for revert reason and bubble it up if present
            if (returndata.length > 0) {
                // The easiest way to bubble the revert reason is using memory via assembly

                assembly {
                    let returndata_size := mload(returndata)
                    revert(add(32, returndata), returndata_size)
                }
            } else {
                revert(errorMessage);
            }
        }
    }
}

abstract contract Context {
    function _msgSender() internal view virtual returns (address) {
        return msg.sender;
    }

    function _msgData() internal view virtual returns (bytes calldata) {
        return msg.data;
    }
}

abstract contract Ownable is Context {
    address private _owner;

    event OwnershipTransferred(
        address indexed previousOwner,
        address indexed newOwner
    );

    constructor() {
        _transferOwnership(_msgSender());
    }

    function owner() public view virtual returns (address) {
        return _owner;
    }

    modifier onlyOwner() {
        require(owner() == _msgSender(), "Ownable: caller is not the owner");
        _;
    }

    function renounceOwnership() public virtual onlyOwner {
        _transferOwnership(address(0));
    }

    function transferOwnership(address newOwner) public virtual onlyOwner {
        require(
            newOwner != address(0),
            "Ownable: new owner is the zero address"
        );
        _transferOwnership(newOwner);
    }

    function _transferOwnership(address newOwner) internal virtual {
        address oldOwner = _owner;
        _owner = newOwner;
        emit OwnershipTransferred(oldOwner, newOwner);
    }
}

contract ERC20 is Context, IERC20, IERC20Metadata {
    mapping(address => uint256) internal _balances;

    mapping(address => mapping(address => uint256)) private _allowances;

    uint256 private _totalSupply;

    string private _name;
    string private _symbol;

    constructor(string memory name_, string memory symbol_) {
        _name = name_;
        _symbol = symbol_;
    }

    function name() public view virtual override returns (string memory) {
        return _name;
    }

    function symbol() public view virtual override returns (string memory) {
        return _symbol;
    }

    function decimals() public view virtual override returns (uint8) {
        return 18;
    }

    function totalSupply() public view virtual override returns (uint256) {
        return _totalSupply;
    }

    function balanceOf(
        address account
    ) public view virtual override returns (uint256) {
        return _balances[account];
    }

    function transfer(
        address recipient,
        uint256 amount
    ) public virtual override returns (bool) {
        _transfer(_msgSender(), recipient, amount);
        return true;
    }

    function allowance(
        address owner,
        address spender
    ) public view virtual override returns (uint256) {
        return _allowances[owner][spender];
    }

    function approve(
        address spender,
        uint256 amount
    ) public virtual override returns (bool) {
        _approve(_msgSender(), spender, amount);
        return true;
    }

    function transferFrom(
        address sender,
        address recipient,
        uint256 amount
    ) public virtual override returns (bool) {
        _transfer(sender, recipient, amount);

        uint256 currentAllowance = _allowances[sender][_msgSender()];
        require(
            currentAllowance >= amount,
            "ERC20: transfer amount exceeds allowance"
        );
        unchecked {
            _approve(sender, _msgSender(), currentAllowance - amount);
        }

        return true;
    }

    function increaseAllowance(
        address spender,
        uint256 addedValue
    ) public virtual returns (bool) {
        _approve(
            _msgSender(),
            spender,
            _allowances[_msgSender()][spender] + addedValue
        );
        return true;
    }

    function decreaseAllowance(
        address spender,
        uint256 subtractedValue
    ) public virtual returns (bool) {
        uint256 currentAllowance = _allowances[_msgSender()][spender];
        require(
            currentAllowance >= subtractedValue,
            "ERC20: decreased allowance below zero"
        );
        unchecked {
            _approve(_msgSender(), spender, currentAllowance - subtractedValue);
        }

        return true;
    }

    function _transfer(
        address sender,
        address recipient,
        uint256 amount
    ) internal virtual {
        require(sender != address(0), "ERC20: transfer from the zero address");
        require(recipient != address(0), "ERC20: transfer to the zero address");

        uint256 senderBalance = _balances[sender];
        require(
            senderBalance >= amount,
            "ERC20: transfer amount exceeds balance"
        );
        unchecked {
            _balances[sender] = senderBalance - amount;
        }
        _balances[recipient] += amount;

        emit Transfer(sender, recipient, amount);
    }

    function _mint(address account, uint256 amount) internal virtual {
        require(account != address(0), "ERC20: mint to the zero address");

        _totalSupply += amount;
        _balances[account] += amount;
        emit Transfer(address(0), account, amount);
    }

    function _burn(address account, uint256 amount) internal virtual {
        require(account != address(0), "ERC20: burn from the zero address");

        uint256 accountBalance = _balances[account];
        require(accountBalance >= amount, "ERC20: burn amount exceeds balance");
        unchecked {
            _balances[account] = accountBalance - amount;
        }
        _totalSupply -= amount;

        emit Transfer(account, address(0), amount);
    }

    function _approve(
        address owner,
        address spender,
        uint256 amount
    ) internal virtual {
        require(owner != address(0), "ERC20: approve from the zero address");
        require(spender != address(0), "ERC20: approve to the zero address");

        _allowances[owner][spender] = amount;
        emit Approval(owner, spender, amount);
    }
}

abstract contract ERC20Burnable is Context, ERC20 {
    function burn(uint256 amount) public virtual {
        _burn(_msgSender(), amount);
    }

    function burnFrom(address account, uint256 amount) public virtual {
        uint256 currentAllowance = allowance(account, _msgSender());
        require(
            currentAllowance >= amount,
            "ERC20: burn amount exceeds allowance"
        );
        unchecked {
            _approve(account, _msgSender(), currentAllowance - amount);
        }
        _burn(account, amount);
    }
}

interface IUniswapV2Factory {
    event PairCreated(
        address indexed token0,
        address indexed token1,
        address pair,
        uint256
    );

    function feeTo() external view returns (address);

    function feeToSetter() external view returns (address);

    function getPair(
        address tokenA,
        address tokenB
    ) external view returns (address pair);

    function allPairs(uint256) external view returns (address pair);

    function allPairsLength() external view returns (uint256);

    function createPair(
        address tokenA,
        address tokenB
    ) external returns (address pair);

    function setFeeTo(address) external;

    function setFeeToSetter(address) external;
}

interface IUniswapV2Pair {
    event Approval(
        address indexed owner,
        address indexed spender,
        uint256 value
    );
    event Transfer(address indexed from, address indexed to, uint256 value);

    function name() external pure returns (string memory);

    function symbol() external pure returns (string memory);

    function decimals() external pure returns (uint8);

    function totalSupply() external view returns (uint256);

    function balanceOf(address owner) external view returns (uint256);

    function allowance(
        address owner,
        address spender
    ) external view returns (uint256);

    function approve(address spender, uint256 value) external returns (bool);

    function transfer(address to, uint256 value) external returns (bool);

    function transferFrom(
        address from,
        address to,
        uint256 value
    ) external returns (bool);

    function DOMAIN_SEPARATOR() external view returns (bytes32);

    function PERMIT_TYPEHASH() external pure returns (bytes32);

    function nonces(address owner) external view returns (uint256);

    function permit(
        address owner,
        address spender,
        uint256 value,
        uint256 deadline,
        uint8 v,
        bytes32 r,
        bytes32 s
    ) external;

    event Burn(
        address indexed sender,
        uint256 amount0,
        uint256 amount1,
        address indexed to
    );
    event Swap(
        address indexed sender,
        uint256 amount0In,
        uint256 amount1In,
        uint256 amount0Out,
        uint256 amount1Out,
        address indexed to
    );
    event Sync(uint112 reserve0, uint112 reserve1);

    function MINIMUM_LIQUIDITY() external pure returns (uint256);

    function factory() external view returns (address);

    function token0() external view returns (address);

    function token1() external view returns (address);

    function getReserves()
        external
        view
        returns (uint112 reserve0, uint112 reserve1, uint32 blockTimestampLast);

    function price0CumulativeLast() external view returns (uint256);

    function price1CumulativeLast() external view returns (uint256);

    function kLast() external view returns (uint256);

    function burn(
        address to
    ) external returns (uint256 amount0, uint256 amount1);

    function swap(
        uint256 amount0Out,
        uint256 amount1Out,
        address to,
        bytes calldata data
    ) external;

    function skim(address to) external;

    function sync() external;

    function initialize(address, address) external;
}

interface IUniswapV2Router01 {
    function factory() external pure returns (address);

    function WETH() external pure returns (address);

    function addLiquidity(
        address tokenA,
        address tokenB,
        uint256 amountADesired,
        uint256 amountBDesired,
        uint256 amountAMin,
        uint256 amountBMin,
        address to,
        uint256 deadline
    ) external returns (uint256 amountA, uint256 amountB, uint256 liquidity);

    function addLiquidityETH(
        address token,
        uint256 amountTokenDesired,
        uint256 amountTokenMin,
        uint256 amountETHMin,
        address to,
        uint256 deadline
    )
        external
        payable
        returns (uint256 amountToken, uint256 amountETH, uint256 liquidity);

    function removeLiquidity(
        address tokenA,
        address tokenB,
        uint256 liquidity,
        uint256 amountAMin,
        uint256 amountBMin,
        address to,
        uint256 deadline
    ) external returns (uint256 amountA, uint256 amountB);

    function removeLiquidityETH(
        address token,
        uint256 liquidity,
        uint256 amountTokenMin,
        uint256 amountETHMin,
        address to,
        uint256 deadline
    ) external returns (uint256 amountToken, uint256 amountETH);

    function removeLiquidityWithPermit(
        address tokenA,
        address tokenB,
        uint256 liquidity,
        uint256 amountAMin,
        uint256 amountBMin,
        address to,
        uint256 deadline,
        bool approveMax,
        uint8 v,
        bytes32 r,
        bytes32 s
    ) external returns (uint256 amountA, uint256 amountB);

    function removeLiquidityETHWithPermit(
        address token,
        uint256 liquidity,
        uint256 amountTokenMin,
        uint256 amountETHMin,
        address to,
        uint256 deadline,
        bool approveMax,
        uint8 v,
        bytes32 r,
        bytes32 s
    ) external returns (uint256 amountToken, uint256 amountETH);

    function swapExactTokensForTokens(
        uint256 amountIn,
        uint256 amountOutMin,
        address[] calldata path,
        address to,
        uint256 deadline
    ) external returns (uint256[] memory amounts);

    function swapTokensForExactTokens(
        uint256 amountOut,
        uint256 amountInMax,
        address[] calldata path,
        address to,
        uint256 deadline
    ) external returns (uint256[] memory amounts);

    function swapExactETHForTokens(
        uint256 amountOutMin,
        address[] calldata path,
        address to,
        uint256 deadline
    ) external payable returns (uint256[] memory amounts);

    function swapTokensForExactETH(
        uint256 amountOut,
        uint256 amountInMax,
        address[] calldata path,
        address to,
        uint256 deadline
    ) external returns (uint256[] memory amounts);

    function swapExactTokensForETH(
        uint256 amountIn,
        uint256 amountOutMin,
        address[] calldata path,
        address to,
        uint256 deadline
    ) external returns (uint256[] memory amounts);

    function swapETHForExactTokens(
        uint256 amountOut,
        address[] calldata path,
        address to,
        uint256 deadline
    ) external payable returns (uint256[] memory amounts);

    function quote(
        uint256 amountA,
        uint256 reserveA,
        uint256 reserveB
    ) external pure returns (uint256 amountB);

    function getAmountOut(
        uint256 amountIn,
        uint256 reserveIn,
        uint256 reserveOut
    ) external pure returns (uint256 amountOut);

    function getAmountIn(
        uint256 amountOut,
        uint256 reserveIn,
        uint256 reserveOut
    ) external pure returns (uint256 amountIn);

    function getAmountsOut(
        uint256 amountIn,
        address[] calldata path
    ) external view returns (uint256[] memory amounts);

    function getAmountsIn(
        uint256 amountOut,
        address[] calldata path
    ) external view returns (uint256[] memory amounts);
}

interface IUniswapV2Router02 is IUniswapV2Router01 {
    function removeLiquidityETHSupportingFeeOnTransferTokens(
        address token,
        uint256 liquidity,
        uint256 amountTokenMin,
        uint256 amountETHMin,
        address to,
        uint256 deadline
    ) external returns (uint256 amountETH);

    function removeLiquidityETHWithPermitSupportingFeeOnTransferTokens(
        address token,
        uint256 liquidity,
        uint256 amountTokenMin,
        uint256 amountETHMin,
        address to,
        uint256 deadline,
        bool approveMax,
        uint8 v,
        bytes32 r,
        bytes32 s
    ) external returns (uint256 amountETH);

    function swapExactTokensForTokensSupportingFeeOnTransferTokens(
        uint256 amountIn,
        uint256 amountOutMin,
        address[] calldata path,
        address to,
        uint256 deadline
    ) external;

    function swapExactETHForTokensSupportingFeeOnTransferTokens(
        uint256 amountOutMin,
        address[] calldata path,
        address to,
        uint256 deadline
    ) external payable;

    function swapExactTokensForETHSupportingFeeOnTransferTokens(
        uint256 amountIn,
        uint256 amountOutMin,
        address[] calldata path,
        address to,
        uint256 deadline
    ) external;
}

contract CoffyDeFi is ERC20Burnable, Ownable {
    using Address for address;

    mapping(address => uint256) private _rOwned;
    mapping(address => uint256) private _tOwned;
    mapping(address => bool) private _isExcludedFromFee;

    mapping(address => bool) private _isExcluded;
    address[] private _excluded;

    uint8 private constant _decimals = 18;

    address payable public marketingAddress = 
        payable(0xeD001ebb1A71dc6df6659c4e4Edb070342fd4a1F);
    address payable public developerAddress = 
        payable(0xb5DF28F0d138275c29536400c1452A816911b77A);
    address public immutable deadAddress =
        0x000000000000000000000000000000000000dEaD;

    uint256 private constant MAX = ~uint256(0);
    uint256 private _tTotal = 1000000000 ether;
    uint256 private _rTotal = (MAX - (MAX % _tTotal));
    uint256 private _tFeeTotal = 0;

    uint256 public _burnFee = 1;
    uint256 private _previousBurnFee = 1;

    uint256 public _reflectionFee = 1;
    uint256 private _previousReflectionFee = 1;

    uint256 public _liquidityPoolFee = 1;
    uint256 private _previousLiquidityPoolFee = 1;

    uint256 public _marketingFee = 1;
    uint256 private _previousMarketingFee = 1;

    uint256 public _developerFee = 1;
    uint256 private _previousDeveloperFee = 1;

    uint256 private _combinedLiquidityFee = 3;
    uint256 private _previousCombinedLiquidityFee = 3;

    uint256 public _maxTxAmount = 5000000 ether;
    uint256 private _previousMaxTxAmount = 5000000 ether;
    uint256 private minimumTokensBeforeSwap = 100000 ether;

    IUniswapV2Router02 public immutable uniswapV2Router;
    address public immutable uniswapV2Pair;

    bool inSwapAndLiquify;
    bool public swapAndLiquifyEnabled = true;

    bool public isPresale = false;

    event BurnFeeUpdated(uint256 oldBurnFee, uint256 newBurnFee);
    event LiquidityPoolFeeUpdated(uint256 oldLiquidityPoolFee, uint256 newLiquidityPoolFee);
    event MarketingFeeUpdated(uint256 oldMarketingFee, uint256 newMarketingFee);
    event DeveloperFeeUpdated(uint256 oldDeveloperFee, uint256 newDeveloperFee);
    event ReflectionFeeUpdated(uint256 oldReflectionFee, uint256 newReflectionFee);
    
    event MaxTxAmountUpdated(uint256 oldMaxTxAmount, uint256 newMaxTxAmount);
    
    event MarketingAddressUpdated(address oldAddress, address newAddress);
    event DeveloperAddressUpdated(address oldAddress, address newAddress);
    
    event PresaleFlagUpdated(bool presale);

    event SwapAndLiquifyEnabledUpdated(bool enabled);
    event SwapAndLiquify(uint256 tokensSwapped, uint256 ethReceived, uint256 tokensIntoLiqudity);
    event SwapAndLiquifyFailed(string message);

    event SwapTokensForETH(uint256 amountIn, address[] path);

    event TransferFailed(address indexed recipient, uint256 amount);

    event EthRecoveredFromContract(address recoveryAddress, uint256 amount);
    event TokensRecoveredFromContract(address tokenAddress, address recoveryAddress, uint256 amount);

    modifier lockTheSwap() {
        inSwapAndLiquify = true;
        _;
        inSwapAndLiquify = false;
    }

    constructor() payable ERC20("Coffy DeFi", "COFFI") {
        IUniswapV2Router02 _uniswapV2Router = 
            IUniswapV2Router02(0x7a250d5630B4cF539739dF2C5dAcb4c659F2488D);
        uniswapV2Pair = IUniswapV2Factory(_uniswapV2Router.factory())
            .createPair(address(this), _uniswapV2Router.WETH());
        uniswapV2Router = _uniswapV2Router;

        _isExcludedFromFee[owner()] = true;
        _isExcludedFromFee[marketingAddress] = true;
        _isExcludedFromFee[developerAddress] = true;
        _isExcludedFromFee[address(this)] = true;

        _mintStart(_msgSender(), _rTotal, _tTotal);
    }

    receive() external payable {}

    function getBalance() private view returns (uint256) {
        return address(this).balance;
    }

    function decimals() public view virtual override returns (uint8) {
        return _decimals;
    }

    function totalSupply() public view virtual override returns (uint256) {
        return _tTotal;
    }

    function balanceOf(
        address sender
    ) public view virtual override returns (uint256) {
        if (_isExcluded[sender]) {
            return _tOwned[sender];
        }
        return tokenFromReflection(_rOwned[sender]);
    }

    function setBurnFee(uint256 burnFee_) external onlyOwner {
        require(
            burnFee_ + _reflectionFee + _liquidityPoolFee + _marketingFee + _developerFee <= 5,
            "Total fees exceed the 5% limit."
        );
        uint256 oldBurnFee = _burnFee;
        _burnFee = burnFee_;
        emit BurnFeeUpdated(oldBurnFee, burnFee_);
    }

    function setReflectionFee(uint256 reflectionFee_) public onlyOwner {
        require(
            _burnFee + reflectionFee_ + _liquidityPoolFee + _marketingFee + _developerFee <= 5,
            "Total fees exceed the 5% limit."
        );
        uint256 oldReflectionFee = _reflectionFee;
        _reflectionFee = reflectionFee_;
        emit ReflectionFeeUpdated(oldReflectionFee, reflectionFee_);
    }

    function setLiquidityPoolFee(uint256 liquidityPoolFee_) external onlyOwner {
        require(
            _burnFee + _reflectionFee + liquidityPoolFee_ + _marketingFee + _developerFee <= 5,
            "Total fees exceed the 5% limit."
        );
        uint256 oldLiquidityPoolFee = _liquidityPoolFee;
        _liquidityPoolFee = liquidityPoolFee_;
        _combinedLiquidityFee = _liquidityPoolFee + _marketingFee + _developerFee;
        emit LiquidityPoolFeeUpdated(oldLiquidityPoolFee, liquidityPoolFee_);
    }

    function setMarketingFee(uint256 marketingFee_) external onlyOwner {
        require(
            _burnFee + _reflectionFee + _liquidityPoolFee + marketingFee_ + _developerFee <= 5,
            "Total fees exceed the 5% limit."
        );
        uint256 oldMarketingFee = _marketingFee;
        _marketingFee = marketingFee_;
        _combinedLiquidityFee = _liquidityPoolFee + _marketingFee + _developerFee;
        emit MarketingFeeUpdated(oldMarketingFee, marketingFee_);
    }

    function setDeveloperFee(uint256 developerFee_) external onlyOwner {
        require(
            _burnFee + _reflectionFee + _liquidityPoolFee + _marketingFee + developerFee_ <= 5,
            "Total fees exceed the 6% limit."
        );
        uint256 oldDeveloperFee = _developerFee;
        _developerFee = developerFee_;
        _combinedLiquidityFee = _liquidityPoolFee + _marketingFee + _developerFee;
        emit DeveloperFeeUpdated(oldDeveloperFee, developerFee_);
    }

    function setMarketingAddress(address _marketingAddress) external onlyOwner {
        require(_marketingAddress != address(0), "Marketing address cannot be the zero address");
        address oldAddress = marketingAddress;
        marketingAddress = payable(_marketingAddress);
        emit MarketingAddressUpdated(oldAddress, _marketingAddress);
    }

    function setDeveloperAddress(address _developerAddress) external onlyOwner {
        require(_developerAddress != address(0), "Developer address cannot be the zero address");
        address oldAddress = developerAddress;
        developerAddress = payable(_developerAddress);
        emit DeveloperAddressUpdated(oldAddress, _developerAddress);
    }

    function setSwapAndLiquifyEnabled(bool _enabled) public onlyOwner {
        swapAndLiquifyEnabled = _enabled;
        emit SwapAndLiquifyEnabledUpdated(_enabled);
    }

    function setMaxTxAmount(uint256 maxTxAmount) external onlyOwner {
        require(
            maxTxAmount >= (_tTotal * 1) / 1000,
            "MaxTxAmount should be at least 0.1% of the total supply."
        );
        uint256 oldMaxTxAmount = _maxTxAmount;
        _maxTxAmount = maxTxAmount;
        emit MaxTxAmountUpdated(oldMaxTxAmount, maxTxAmount);
    }

    function isExcludedFromFee(address account) public view returns (bool) {
        return _isExcludedFromFee[account];
    }

    function excludeFromFee(address account) public onlyOwner {
        _isExcludedFromFee[account] = true;
    }

    function includeInFee(address account) public onlyOwner {
        _isExcludedFromFee[account] = false;
    }

    function isExcluded(address account) public view returns (bool) {
        return _isExcluded[account];
    }

    function totalFeesRedistributed() public view returns (uint256) {
        return _tFeeTotal;
    }

    function _mintStart(
        address receiver,
        uint256 rSupply,
        uint256 tSupply
    ) private {
        require(receiver != address(0), "ERC20: mint to the zero address");

        _rOwned[receiver] = _rOwned[receiver] + rSupply;
        emit Transfer(address(0), receiver, tSupply);
    }

    function reflect(uint256 tAmount) public {
        address sender = _msgSender();
        require(
            !_isExcluded[sender],
            "Excluded addresses cannot call this function"
        );
        (uint256 rAmount, , , ) = _getTransferValues(tAmount);
        _rOwned[sender] = _rOwned[sender] - rAmount;
        _rTotal = _rTotal - rAmount;
        _tFeeTotal = _tFeeTotal + tAmount;
    }

    function reflectionFromToken(
        uint256 tAmount,
        bool deductTransferFee
    ) public view returns (uint256) {
        require(tAmount <= _tTotal, "Amount must be less than supply");
        if (!deductTransferFee) {
            (uint256 rAmount, , , ) = _getTransferValues(tAmount);
            return rAmount;
        } else {
            (, uint256 rTransferAmount, , ) = _getTransferValues(tAmount);
            return rTransferAmount;
        }
    }

    function tokenFromReflection(
        uint256 rAmount
    ) private view returns (uint256) {
        require(
            rAmount <= _rTotal,
            "Amount must be less than total reflections"
        );
        uint256 currentRate = _getRate();
        return rAmount / currentRate;
    }

    function excludeAccountFromReward(address account) public onlyOwner {
        require(!_isExcluded[account], "Account is already excluded");
        require(
            account != address(this),
            "Contract address cannot be excluded from reflection"
        );
        if (_rOwned[account] > 0) {
            _tOwned[account] = tokenFromReflection(_rOwned[account]);
        }
        _isExcluded[account] = true;
        _excluded.push(account);
    }

    function includeAccountinReward(address account) public onlyOwner {
        require(_isExcluded[account], "Account is already included");
        for (uint256 i = 0; i < _excluded.length; i++) {
            if (_excluded[i] == account) {
                _excluded[i] = _excluded[_excluded.length - 1];
                _tOwned[account] = 0;
                _isExcluded[account] = false;
                _excluded.pop();
                break;
            }
        }
    }

    function _transfer(
        address sender,
        address recipient,
        uint256 amount
    ) internal virtual override {
        require(sender != address(0), "ERC20: transfer from the zero address");
        require(recipient != address(0), "ERC20: transfer to the zero address");
        require(amount > 0, "Transfer amount must be greater than zero");
        uint256 senderBalance = balanceOf(sender);
        require(
            senderBalance >= amount,
            "ERC20: transfer amount exceeds balance"
        );
        if (sender != owner() && recipient != owner()) {
            require(
                amount <= _maxTxAmount,
                "Transfer amount exceeds the maxTxAmount."
            );
        }

        uint256 contractTokenBalance = balanceOf(address(this));
        bool overMinimumTokenBalance = contractTokenBalance >=
            minimumTokensBeforeSwap;

        if (
            !inSwapAndLiquify &&
            swapAndLiquifyEnabled &&
            recipient == uniswapV2Pair
        ) {
            if (overMinimumTokenBalance) {
                contractTokenBalance = minimumTokensBeforeSwap;
                swapTokens(contractTokenBalance);
            }
        }

        bool takeFee = true;

        if (_isExcludedFromFee[sender] || _isExcludedFromFee[recipient]) {
            takeFee = false;
        }

        _tokenTransfer(sender, recipient, amount, takeFee);
    }

    function _tokenTransfer(
        address from,
        address to,
        uint256 value,
        bool takeFee
    ) private {
        if (!takeFee) {
            removeAllFee();
        }

        _transferStandard(from, to, value);

        if (!takeFee) {
            restoreAllFee();
        }
    }

    function _transferStandard(
        address sender,
        address recipient,
        uint256 tAmount
    ) private {
        (
            uint256 rAmount,
            uint256 rTransferAmount,
            uint256 tTransferAmount,
            uint256 currentRate
        ) = _getTransferValues(tAmount);

        _rOwned[sender] = _rOwned[sender] - rAmount;
        _rOwned[recipient] = _rOwned[recipient] + rTransferAmount;

        if (_isExcluded[sender] && !_isExcluded[recipient]) {
            _tOwned[sender] = _tOwned[sender] - tAmount;
        } else if (!_isExcluded[sender] && _isExcluded[recipient]) {
            _tOwned[recipient] = _tOwned[recipient] + tTransferAmount;
        } else if (_isExcluded[sender] && _isExcluded[recipient]) {
            _tOwned[sender] = _tOwned[sender] - tAmount;
            _tOwned[recipient] = _tOwned[recipient] + tTransferAmount;
        }

        _reflectFee(tAmount, currentRate);
        burnFeeTransfer(sender, tAmount, currentRate);
        feeTransfer(
            sender,
            tAmount,
            currentRate,
            _combinedLiquidityFee,
            address(this)
        );

        emit Transfer(sender, recipient, tTransferAmount);
    }

    function _getTransferValues(
        uint256 tAmount
    ) private view returns (uint256, uint256, uint256, uint256) {
        uint256 taxValue = _getCompleteTaxValue(tAmount);
        uint256 tTransferAmount = tAmount - taxValue;
        uint256 currentRate = _getRate();
        uint256 rTransferAmount = tTransferAmount * currentRate;
        uint256 rAmount = tAmount * currentRate;
        return (rAmount, rTransferAmount, tTransferAmount, currentRate);
    }

    function _getCompleteTaxValue(
        uint256 amount
    ) private view returns (uint256) {
        uint256 allTaxes = _combinedLiquidityFee + _reflectionFee + _burnFee;
        uint256 taxValue = (amount * allTaxes) / 100;
        return taxValue;
    }

    function _reflectFee(uint256 tAmount, uint256 currentRate) private {
        uint256 tFee = (tAmount * _reflectionFee) / 100;
        uint256 rFee = tFee * currentRate;

        _rTotal = _rTotal - rFee;
        _tFeeTotal = _tFeeTotal + tFee;
    }

    function burnFeeTransfer(
        address sender,
        uint256 tAmount,
        uint256 currentRate
    ) private {
        uint256 tBurnFee = (tAmount * _burnFee) / 100;
        if (tBurnFee > 0) {
            uint256 rBurnFee = tBurnFee * currentRate;
            _tTotal = _tTotal - tBurnFee;
            _rTotal = _rTotal - rBurnFee;
            emit Transfer(sender, address(0), tBurnFee);
        }
    }

    function feeTransfer(
        address sender,
        uint256 tAmount,
        uint256 currentRate,
        uint256 fee,
        address receiver
    ) private {
        uint256 tFee = (tAmount * fee) / 100;
        if (tFee > 0) {
            uint256 rFee = tFee * currentRate;
            _rOwned[receiver] = _rOwned[receiver] + rFee;
            emit Transfer(sender, receiver, tFee);
        }
    }

    function _getRate() private view returns (uint256) {
        (uint256 rSupply, uint256 tSupply) = _getCurrentSupply();
        return rSupply / tSupply;
    }

    function _getCurrentSupply() private view returns (uint256, uint256) {
        uint256 rSupply = _rTotal;
        uint256 tSupply = _tTotal;

        for (uint256 i = 0; i < _excluded.length; i++) {
            if (
                _rOwned[_excluded[i]] > rSupply ||
                _tOwned[_excluded[i]] > tSupply
            ) {
                return (_rTotal, _tTotal);
            }
            rSupply = rSupply - _rOwned[_excluded[i]];
            tSupply = tSupply - _tOwned[_excluded[i]];
        }

        if (rSupply < _rTotal / _tTotal) {
            return (_rTotal, _tTotal);
        }

        return (rSupply, tSupply);
    }

    function swapTokens(uint256 contractTokenBalance) private lockTheSwap {
        if (_combinedLiquidityFee > 0) {
            uint256 initialBalance = address(this).balance;
            uint256 lpTokenBalance = (contractTokenBalance * _liquidityPoolFee) /
                _combinedLiquidityFee;

            uint256 liquidityHalf = lpTokenBalance / 2;
            uint256 otherLiquidityHalf = lpTokenBalance - liquidityHalf;
            swapTokensForEth(contractTokenBalance - otherLiquidityHalf);

            uint256 transferredBalance = address(this).balance - initialBalance;

            transferToAddressETH(
                marketingAddress,
                ((transferredBalance) * (_marketingFee * 10)) /
                    (_combinedLiquidityFee * 10 - ((_liquidityPoolFee * 10) / 2))
            );
            transferToAddressETH(
                developerAddress,
                ((transferredBalance) * (_developerFee * 10)) /
                    (_combinedLiquidityFee * 10 - ((_liquidityPoolFee * 10) / 2))
            );

            uint256 liquidityBalance = 
                ((transferredBalance * _liquidityPoolFee * 10) / 2) /
                ((_combinedLiquidityFee * 10) - ((_liquidityPoolFee * 10) / 2));

            addLiquidity(otherLiquidityHalf, liquidityBalance);

            emit SwapAndLiquify(
                liquidityHalf,
                liquidityBalance,
                otherLiquidityHalf
            );
        } else {
            emit SwapAndLiquifyFailed("_combinedLiquidityFee is 0, skipping swapAndLiquify.");
        }
    }

    function swapTokensForEth(uint256 tokenAmount) private {
        address[] memory path = new address[](2);
        path[0] = address(this);
        path[1] = uniswapV2Router.WETH();

        _approve(address(this), address(uniswapV2Router), tokenAmount);

        uniswapV2Router.swapExactTokensForETHSupportingFeeOnTransferTokens(
            tokenAmount,
            0, // accept any amount of ETH
            path,
            address(this),
            block.timestamp
        );

        emit SwapTokensForETH(tokenAmount, path);
    }

    function addLiquidity(uint256 tokenAmount, uint256 ethAmount) private {
        _approve(address(this), address(uniswapV2Router), tokenAmount);

        uniswapV2Router.addLiquidityETH{value: ethAmount}(
            address(this),
            tokenAmount,
            0,
            0,
            owner(),
            block.timestamp
        );
    }

    function removeAllFee() private {
        _previousCombinedLiquidityFee = _combinedLiquidityFee;
        _previousLiquidityPoolFee = _liquidityPoolFee;
        _previousBurnFee = _burnFee;
        _previousReflectionFee = _reflectionFee;
        _previousMarketingFee = _marketingFee;
        _previousDeveloperFee = _developerFee;

        _combinedLiquidityFee = 0;
        _liquidityPoolFee = 0;
        _burnFee = 0;
        _reflectionFee = 0;
        _marketingFee = 0;
        _developerFee = 0;
    }

    function restoreAllFee() private {
        _combinedLiquidityFee = _previousCombinedLiquidityFee;
        _liquidityPoolFee = _previousLiquidityPoolFee;
        _burnFee = _previousBurnFee;
        _reflectionFee = _previousReflectionFee;
        _marketingFee = _previousMarketingFee;
        _developerFee = _previousDeveloperFee;
    }

    function presale(bool _presale) external onlyOwner {
        require(_presale != isPresale, "Set a different value.");
        if (_presale) {
            setSwapAndLiquifyEnabled(false);
            removeAllFee();
            _previousMaxTxAmount = _maxTxAmount;
            _maxTxAmount = totalSupply();
        } else {
            setSwapAndLiquifyEnabled(true);
            restoreAllFee();
            _maxTxAmount = _previousMaxTxAmount;
        }
        isPresale = _presale;
        emit PresaleFlagUpdated(_presale);
    }

    function transferToAddressETH(
        address payable recipient,
        uint256 amount
    ) private {
        (bool success, ) = recipient.call{value: amount}("");
        if (!success) {
            emit TransferFailed(recipient, amount);
        }
    }

    function _burn(address account, uint256 amount) internal virtual override {
        require(account != address(0), "ERC20: burn from the zero address");
        uint256 accountBalance = balanceOf(account);
        require(accountBalance >= amount, "ERC20: burn amount exceeds balance");

        uint256 currentRate = _getRate();
        uint256 rAmount = amount * currentRate;

        if (_isExcluded[account]) {
            _tOwned[account] = _tOwned[account] - amount;
        }

        _rOwned[account] = _rOwned[account] - rAmount;

        _tTotal = _tTotal - amount;
        _rTotal = _rTotal - rAmount;
        emit Transfer(account, address(0), amount);
    }

    function recoverETHfromContract() external onlyOwner {
        uint ethBalance = address(this).balance;
        (bool succ, ) = payable(developerAddress).call{value: ethBalance}("");
        require(succ, "Transfer failed");
        emit EthRecoveredFromContract(developerAddress, ethBalance);
    }

    function recoverTokensFromContract(
        address _tokenAddress,
        uint256 _amount
    ) external onlyOwner {
        require(
            _tokenAddress != address(this),
            "Owner can't claim contract's balance of its own tokens"
        );
        bool success = IERC20(_tokenAddress).transfer(developerAddress, _amount);
        require(success, "Transfer failed");
        emit TokensRecoveredFromContract(_tokenAddress, developerAddress, _amount);
    }
}