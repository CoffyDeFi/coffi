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

/**
 * @dev Interface of the ERC20 standard as defined in the EIP.
 */
interface IERC20 {
    /**
     * @dev Returns the amount of tokens in existence.
     */
    function totalSupply() external view returns (uint256);

    /**
     * @dev Returns the amount of tokens owned by `account`.
     */
    function balanceOf(address account) external view returns (uint256);

    /**
     * @dev Moves `amount` tokens from the caller's account to `recipient`.
     *
     * Returns a boolean value indicating whether the operation succeeded.
     *
     * Emits a {Transfer} event.
     */
    function transfer(
        address recipient,
        uint256 amount
    ) external returns (bool);

    /**
     * @dev Returns the remaining number of tokens that `spender` will be
     * allowed to spend on behalf of `owner` through {transferFrom}. This is
     * zero by default.
     *
     * This value changes when {approve} or {transferFrom} are called.
     */
    function allowance(
        address owner,
        address spender
    ) external view returns (uint256);

    /**
     * @dev Sets `amount` as the allowance of `spender` over the caller's tokens.
     *
     * Returns a boolean value indicating whether the operation succeeded.
     *
     * IMPORTANT: Beware that changing an allowance with this method brings the risk
     * that someone may use both the old and the new allowance by unfortunate
     * transaction ordering. One possible solution to mitigate this race
     * condition is to first reduce the spender's allowance to 0 and set the
     * desired value afterwards:
     * https://github.com/ethereum/EIPs/issues/20#issuecomment-263524729
     *
     * Emits an {Approval} event.
     */
    function approve(address spender, uint256 amount) external returns (bool);

    /**
     * @dev Moves `amount` tokens from `sender` to `recipient` using the
     * allowance mechanism. `amount` is then deducted from the caller's
     * allowance.
     *
     * Returns a boolean value indicating whether the operation succeeded.
     *
     * Emits a {Transfer} event.
     */
    function transferFrom(
        address sender,
        address recipient,
        uint256 amount
    ) external returns (bool);

    /**
     * @dev Emitted when `value` tokens are moved from one account (`from`) to
     * another (`to`).
     *
     * Note that `value` may be zero.
     */
    event Transfer(address indexed from, address indexed to, uint256 value);

    /**
     * @dev Emitted when the allowance of a `spender` for an `owner` is set by
     * a call to {approve}. `value` is the new allowance.
     */
    event Approval(
        address indexed owner,
        address indexed spender,
        uint256 value
    );
}

/**
 * @dev Interface for the optional metadata functions from the ERC20 standard.
 *
 * _Available since v4.1._
 */
interface IERC20Metadata is IERC20 {
    /**
     * @dev Returns the name of the token.
     */
    function name() external view returns (string memory);

    /**
     * @dev Returns the symbol of the token.
     */
    function symbol() external view returns (string memory);

    /**
     * @dev Returns the decimals places of the token.
     */
    function decimals() external view returns (uint8);
}

/**
 * @dev Collection of functions related to the address type
 */
library Address {
    /**
     * @dev Returns true if `account` is a contract.
     *
     * [IMPORTANT]
     * ====
     * It is unsafe to assume that an address for which this function returns
     * false is an externally-owned account (EOA) and not a contract.
     *
     * Among others, `isContract` will return false for the following
     * types of addresses:
     *
     *  - an externally-owned account
     *  - a contract in construction
     *  - an address where a contract will be created
     *  - an address where a contract lived, but was destroyed
     * ====
     *
     * [IMPORTANT]
     * ====
     * You shouldn't rely on `isContract` to protect against flash loan attacks!
     *
     * Preventing calls from contracts is highly discouraged. It breaks composability, breaks support for smart wallets
     * like Gnosis Safe, and does not provide security since it can be circumvented by calling from a contract
     * constructor.
     * ====
     */
    function isContract(address account) internal view returns (bool) {
        // This method relies on extcodesize/address.code.length, which returns 0
        // for contracts in construction, since the code is only stored at the end
        // of the constructor execution.

        return account.code.length > 0;
    }

    /**
     * @dev Replacement for Solidity's `transfer`: sends `amount` wei to
     * `recipient`, forwarding all available gas and reverting on errors.
     *
     * https://eips.ethereum.org/EIPS/eip-1884[EIP1884] increases the gas cost
     * of certain opcodes, possibly making contracts go over the 2300 gas limit
     * imposed by `transfer`, making them unable to receive funds via
     * `transfer`. {sendValue} removes this limitation.
     *
     * https://diligence.consensys.net/posts/2019/09/stop-using-soliditys-transfer-now/[Learn more].
     *
     * IMPORTANT: because control is transferred to `recipient`, care must be
     * taken to not create reentrancy vulnerabilities. Consider using
     * {ReentrancyGuard} or the
     * https://solidity.readthedocs.io/en/v0.5.11/security-considerations.html#use-the-checks-effects-interactions-pattern[checks-effects-interactions pattern].
     */
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

    /**
     * @dev Performs a Solidity function call using a low level `call`. A
     * plain `call` is an unsafe replacement for a function call: use this
     * function instead.
     *
     * If `target` reverts with a revert reason, it is bubbled up by this
     * function (like regular Solidity function calls).
     *
     * Returns the raw returned data. To convert to the expected return value,
     * use https://solidity.readthedocs.io/en/latest/units-and-global-variables.html?highlight=abi.decode#abi-encoding-and-decoding-functions[`abi.decode`].
     *
     * Requirements:
     *
     * - `target` must be a contract.
     * - calling `target` with `data` must not revert.
     *
     * _Available since v3.1._
     */
    function functionCall(
        address target,
        bytes memory data
    ) internal returns (bytes memory) {
        return functionCall(target, data, "Address: low-level call failed");
    }

    /**
     * @dev Same as {xref-Address-functionCall-address-bytes-}[`functionCall`], but with
     * `errorMessage` as a fallback revert reason when `target` reverts.
     *
     * _Available since v3.1._
     */
    function functionCall(
        address target,
        bytes memory data,
        string memory errorMessage
    ) internal returns (bytes memory) {
        return functionCallWithValue(target, data, 0, errorMessage);
    }

    /**
     * @dev Same as {xref-Address-functionCall-address-bytes-}[`functionCall`],
     * but also transferring `value` wei to `target`.
     *
     * Requirements:
     *
     * - the calling contract must have an ETH balance of at least `value`.
     * - the called Solidity function must be `payable`.
     *
     * _Available since v3.1._
     */
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

    /**
     * @dev Same as {xref-Address-functionCallWithValue-address-bytes-uint256-}[`functionCallWithValue`], but
     * with `errorMessage` as a fallback revert reason when `target` reverts.
     *
     * _Available since v3.1._
     */
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

    /**
     * @dev Same as {xref-Address-functionCall-address-bytes-}[`functionCall`],
     * but performing a static call.
     *
     * _Available since v3.3._
     */
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

    /**
     * @dev Same as {xref-Address-functionCall-address-bytes-string-}[`functionCall`],
     * but performing a static call.
     *
     * _Available since v3.3._
     */
    function functionStaticCall(
        address target,
        bytes memory data,
        string memory errorMessage
    ) internal view returns (bytes memory) {
        require(isContract(target), "Address: static call to non-contract");

        (bool success, bytes memory returndata) = target.staticcall(data);
        return verifyCallResult(success, returndata, errorMessage);
    }

    /**
     * @dev Same as {xref-Address-functionCall-address-bytes-}[`functionCall`],
     * but performing a delegate call.
     *
     * _Available since v3.4._
     */
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

    /**
     * @dev Same as {xref-Address-functionCall-address-bytes-string-}[`functionCall`],
     * but performing a delegate call.
     *
     * _Available since v3.4._
     */
    function functionDelegateCall(
        address target,
        bytes memory data,
        string memory errorMessage
    ) internal returns (bytes memory) {
        require(isContract(target), "Address: delegate call to non-contract");

        (bool success, bytes memory returndata) = target.delegatecall(data);
        return verifyCallResult(success, returndata, errorMessage);
    }

    /**
     * @dev Tool to verifies that a low level call was successful, and revert if it wasn't, either by bubbling the
     * revert reason using the provided one.
     *
     * _Available since v4.3._
     */
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

/**
 * @dev Provides information about the current execution context, including the
 * sender of the transaction and its data. While these are generally available
 * via msg.sender and msg.data, they should not be accessed in such a direct
 * manner, since when dealing with meta-transactions the account sending and
 * paying for execution may not be the actual sender (as far as an application
 * is concerned).
 *
 * This contract is only required for intermediate, library-like contracts.
 */
abstract contract Context {
    function _msgSender() internal view virtual returns (address) {
        return msg.sender;
    }

    function _msgData() internal view virtual returns (bytes calldata) {
        return msg.data;
    }
}

/**
 * @dev Contract module which provides a basic access control mechanism, where
 * there is an account (an owner) that can be granted exclusive access to
 * specific functions.
 *
 * By default, the owner account will be the one that deploys the contract. This
 * can later be changed with {transferOwnership}.
 *
 * This module is used through inheritance. It will make available the modifier
 * `onlyOwner`, which can be applied to your functions to restrict their use to
 * the owner.
 */
abstract contract Ownable is Context {
    address private _owner;

    event OwnershipTransferred(
        address indexed previousOwner,
        address indexed newOwner
    );

    /**
     * @dev Initializes the contract setting the deployer as the initial owner.
     */
    constructor() {
        _transferOwnership(_msgSender());
    }

    /**
     * @dev Returns the address of the current owner.
     */
    function owner() public view virtual returns (address) {
        return _owner;
    }

    /**
     * @dev Throws if called by any account other than the owner.
     */
    modifier onlyOwner() {
        require(owner() == _msgSender(), "Ownable: caller is not the owner");
        _;
    }

    /**
     * @dev Leaves the contract without owner. It will not be possible to call
     * `onlyOwner` functions anymore. Can only be called by the current owner.
     *
     * NOTE: Renouncing ownership will leave the contract without an owner,
     * thereby removing any functionality that is only available to the owner.
     */
    function renounceOwnership() public virtual onlyOwner {
        _transferOwnership(address(0));
    }

    /**
     * @dev Transfers ownership of the contract to a new account (`newOwner`).
     * Can only be called by the current owner.
     */
    function transferOwnership(address newOwner) public virtual onlyOwner {
        require(
            newOwner != address(0),
            "Ownable: new owner is the zero address"
        );
        _transferOwnership(newOwner);
    }

    /**
     * @dev Transfers ownership of the contract to a new account (`newOwner`).
     * Internal function without access restriction.
     */
    function _transferOwnership(address newOwner) internal virtual {
        address oldOwner = _owner;
        _owner = newOwner;
        emit OwnershipTransferred(oldOwner, newOwner);
    }
}

/**
 * @dev Implementation of the {IERC20} interface.
 *
 * This implementation is agnostic to the way tokens are created. This means
 * that a supply mechanism has to be added in a derived contract using {_mint}.
 * For a generic mechanism see {ERC20PresetMinterPauser}.
 *
 * TIP: For a detailed writeup see our guide
 * https://forum.zeppelin.solutions/t/how-to-implement-erc20-supply-mechanisms/226[How
 * to implement supply mechanisms].
 *
 * We have followed general OpenZeppelin Contracts guidelines: functions revert
 * instead returning `false` on failure. This behavior is nonetheless
 * conventional and does not conflict with the expectations of ERC20
 * applications.
 *
 * Additionally, an {Approval} event is emitted on calls to {transferFrom}.
 * This allows applications to reconstruct the allowance for all accounts just
 * by listening to said events. Other implementations of the EIP may not emit
 * these events, as it isn't required by the specification.
 *
 * Finally, the non-standard {decreaseAllowance} and {increaseAllowance}
 * functions have been added to mitigate the well-known issues around setting
 * allowances. See {IERC20-approve}.
 */
contract ERC20 is Context, IERC20, IERC20Metadata {
    mapping(address => uint256) internal _balances;

    mapping(address => mapping(address => uint256)) private _allowances;

    uint256 private _totalSupply;

    string private _name;
    string private _symbol;

    /**
     * @dev Sets the values for {name} and {symbol}.
     *
     * The default value of {decimals} is 18. To select a different value for
     * {decimals} you should overload it.
     *
     * All two of these values are immutable: they can only be set once during
     * construction.
     */
    constructor(string memory name_, string memory symbol_) {
        _name = name_;
        _symbol = symbol_;
    }

    /**
     * @dev Returns the name of the token.
     */
    function name() public view virtual override returns (string memory) {
        return _name;
    }

    /**
     * @dev Returns the symbol of the token, usually a shorter version of the
     * name.
     */
    function symbol() public view virtual override returns (string memory) {
        return _symbol;
    }

    /**
     * @dev Returns the number of decimals used to get its user representation.
     * For example, if `decimals` equals `2`, a balance of `505` tokens should
     * be displayed to a user as `5.05` (`505 / 10 ** 2`).
     *
     * Tokens usually opt for a value of 18, imitating the relationship between
     * Ether and Wei. This is the value {ERC20} uses, unless this function is
     * overridden;
     *
     * NOTE: This information is only used for _display_ purposes: it in
     * no way affects any of the arithmetic of the contract, including
     * {IERC20-balanceOf} and {IERC20-transfer}.
     */
    function decimals() public view virtual override returns (uint8) {
        return 18;
    }

    /**
     * @dev See {IERC20-totalSupply}.
     */
    function totalSupply() public view virtual override returns (uint256) {
        return _totalSupply;
    }

    /**
     * @dev See {IERC20-balanceOf}.
     */
    function balanceOf(
        address account
    ) public view virtual override returns (uint256) {
        return _balances[account];
    }

    /**
     * @dev See {IERC20-transfer}.
     *
     * Requirements:
     *
     * - `recipient` cannot be the zero address.
     * - the caller must have a balance of at least `amount`.
     */
    function transfer(
        address recipient,
        uint256 amount
    ) public virtual override returns (bool) {
        _transfer(_msgSender(), recipient, amount);
        return true;
    }

    /**
     * @dev See {IERC20-allowance}.
     */
    function allowance(
        address owner,
        address spender
    ) public view virtual override returns (uint256) {
        return _allowances[owner][spender];
    }

    /**
     * @dev See {IERC20-approve}.
     *
     * Requirements:
     *
     * - `spender` cannot be the zero address.
     */
    function approve(
        address spender,
        uint256 amount
    ) public virtual override returns (bool) {
        _approve(_msgSender(), spender, amount);
        return true;
    }

    /**
     * @dev See {IERC20-transferFrom}.
     *
     * Emits an {Approval} event indicating the updated allowance. This is not
     * required by the EIP. See the note at the beginning of {ERC20}.
     *
     * Requirements:
     *
     * - `sender` and `recipient` cannot be the zero address.
     * - `sender` must have a balance of at least `amount`.
     * - the caller must have allowance for ``sender``'s tokens of at least
     * `amount`.
     */
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

    /**
     * @dev Atomically increases the allowance granted to `spender` by the caller.
     *
     * This is an alternative to {approve} that can be used as a mitigation for
     * problems described in {IERC20-approve}.
     *
     * Emits an {Approval} event indicating the updated allowance.
     *
     * Requirements:
     *
     * - `spender` cannot be the zero address.
     */
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

    /**
     * @dev Atomically decreases the allowance granted to `spender` by the caller.
     *
     * This is an alternative to {approve} that can be used as a mitigation for
     * problems described in {IERC20-approve}.
     *
     * Emits an {Approval} event indicating the updated allowance.
     *
     * Requirements:
     *
     * - `spender` cannot be the zero address.
     * - `spender` must have allowance for the caller of at least
     * `subtractedValue`.
     */
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

    /**
     * @dev Moves `amount` of tokens from `sender` to `recipient`.
     *
     * This internal function is equivalent to {transfer}, and can be used to
     * e.g. implement automatic token fees, slashing mechanisms, etc.
     *
     * Emits a {Transfer} event.
     *
     * Requirements:
     *
     * - `sender` cannot be the zero address.
     * - `recipient` cannot be the zero address.
     * - `sender` must have a balance of at least `amount`.
     */
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

    /** @dev Creates `amount` tokens and assigns them to `account`, increasing
     * the total supply.
     *
     * Emits a {Transfer} event with `from` set to the zero address.
     *
     * Requirements:
     *
     * - `account` cannot be the zero address.
     */
    function _mint(address account, uint256 amount) internal virtual {
        require(account != address(0), "ERC20: mint to the zero address");

        _totalSupply += amount;
        _balances[account] += amount;
        emit Transfer(address(0), account, amount);
    }

    /**
     * @dev Destroys `amount` tokens from `account`, reducing the
     * total supply.
     *
     * Emits a {Transfer} event with `to` set to the zero address.
     *
     * Requirements:
     *
     * - `account` cannot be the zero address.
     * - `account` must have at least `amount` tokens.
     */
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

    /**
     * @dev Sets `amount` as the allowance of `spender` over the `owner` s tokens.
     *
     * This internal function is equivalent to `approve`, and can be used to
     * e.g. set automatic allowances for certain subsystems, etc.
     *
     * Emits an {Approval} event.
     *
     * Requirements:
     *
     * - `owner` cannot be the zero address.
     * - `spender` cannot be the zero address.
     */
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

/**
 * @dev Extension of {ERC20} that allows token holders to destroy both their own
 * tokens and those that they have an allowance for, in a way that can be
 * recognized off-chain (via event analysis).
 */
abstract contract ERC20Burnable is Context, ERC20 {
    /**
     * @dev Destroys `amount` tokens from the caller.
     *
     * See {ERC20-_burn}.
     */
    function burn(uint256 amount) public virtual {
        _burn(_msgSender(), amount);
    }

    /**
     * @dev Destroys `amount` tokens from `account`, deducting from the caller's
     * allowance.
     *
     * See {ERC20-_burn} and {ERC20-allowance}.
     *
     * Requirements:
     *
     * - the caller must have allowance for ``accounts``'s tokens of at least
     * `amount`.
     */
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

// pragma solidity >=0.5.0;

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

// pragma solidity >=0.5.0;

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

// pragma solidity >=0.6.2;

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

// pragma solidity >=0.6.2;

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
    address payable public charityAddress = 
        payable(0x2C9BaD149BEF185d6B90daf9857AbA8841f4dC84);
    address public constant deadAddress =
        0x000000000000000000000000000000000000dEaD;

    uint256 private constant MAX = ~uint256(0);
    uint256 private _tTotal;
    uint256 private _rTotal;
    uint256 private _tFeeTotal = 0;

    uint256 public constant MAX_TOTAL_FEES = 5; // Max Tx Fee for COFFI is never going to exceed 5%
    uint256 public constant MAX_BURN_FEE = 1;
    uint256 public constant MAX_FEE_INDIVIDUAL = 2;
    uint256 public constant MIN_COMBINED_LIQUIDITY_FEE = 1;

    uint256 public _reflectionFee;
    uint256 private _previousReflectionFee;

    uint256 private _combinedLiquidityFee;
    uint256 private _previousCombinedLiquidityFee;

    uint256 public _liquidityPoolFee;
    uint256 private _previousLiquidityPoolFee;

    uint256 public _burnFee;
    uint256 private _previousBurnFee;

    uint256 public _marketingFee;
    uint256 private _previousMarketingFee;

    uint256 public _developerFee;
    uint256 private _previousDeveloperFee;

    uint256 public _charityFee;
    uint256 private _previousCharityFee;

    uint256 public _maxTxAmount;
    uint256 private _previousMaxTxAmount;
    uint256 private minimumTokensBeforeSwap;

    IUniswapV2Router02 public immutable uniswapV2Router;
    address public immutable uniswapV2Pair;

    bool inSwapAndLiquify;
    bool public swapAndLiquifyEnabled = true;

    event BurnFeeUpdated(uint256 oldBurnFee, uint256 newBurnFee);
    event LiquidityPoolFeeUpdated(uint256 oldLiquidityPoolFee, uint256 newLiquidityPoolFee);
    event MarketingFeeUpdated(uint256 oldMarketingFee, uint256 newMarketingFee);
    event DeveloperFeeUpdated(uint256 oldDeveloperFee, uint256 newDeveloperFee);
    event CharityFeeUpdated(uint256 oldCharityFee, uint256 newCharityFee);
    event ReflectionFeeUpdated(uint256 oldReflectionFee, uint256 newReflectionFee);
    event MinimumTokensBeforeSwapUpdated(uint256 oldMinimumTokensBeforeSwap, uint256 newMinimumTokensBeforeSwap);
    event MaxTxAmountUpdated(uint256 oldMaxTxAmount, uint256 newMaxTxAmount);
    event MarketingAddressUpdated(address oldAddress, address newAddress);
    event DeveloperAddressUpdated(address oldAddress, address newAddress);
    event CharityAddressUpdated(address oldAddress, address newAddress);
    event PresaleFlagUpdated(bool presale);

    event SwapAndLiquifyEnabledUpdated(bool enabled);
    event SwapAndLiquify(
        uint256 tokensSwapped,
        uint256 ethReceived,
        uint256 tokensIntoLiqudity
    );

    event SwapETHForTokens(uint256 amountIn, address[] path);

    event SwapTokensForETH(uint256 amountIn, address[] path);

    event TransferFailed(address indexed recipient, uint256 amount);

    event Log(string, uint256);
    event AuditLog(string, address);

    modifier lockTheSwap() {
        inSwapAndLiquify = true;
        _;
        inSwapAndLiquify = false;
    }

    constructor() payable ERC20("Coffy DeFi", "COFFI") {
        _tTotal = 1000000000 * 10 ** _decimals;
        _rTotal = (MAX - (MAX % _tTotal));

        _reflectionFee = 1;
        _previousReflectionFee = _reflectionFee;

        _liquidityPoolFee = 1;
        _previousLiquidityPoolFee = _liquidityPoolFee;

        _burnFee = 1;
        _previousBurnFee = _burnFee;

        _marketingFee = 1;
        _previousMarketingFee = _marketingFee;
        
        _developerFee = 1;
        _previousDeveloperFee = _developerFee;
        
        _charityFee = 0;
        _previousCharityFee = _charityFee;

        _combinedLiquidityFee = _marketingFee + _developerFee + _charityFee + _liquidityPoolFee;
        _previousCombinedLiquidityFee = _combinedLiquidityFee;

        _maxTxAmount = (_tTotal * 5) / 1000;
        _previousMaxTxAmount = _maxTxAmount;

        minimumTokensBeforeSwap = (_tTotal * 2) / 10000;

        IUniswapV2Router02 _uniswapV2Router = IUniswapV2Router02(0x7a250d5630B4cF539739dF2C5dAcb4c659F2488D);
        uniswapV2Pair = IUniswapV2Factory(_uniswapV2Router.factory())
            .createPair(address(this), _uniswapV2Router.WETH());
        uniswapV2Router = _uniswapV2Router;
        _approve(address(this), address(uniswapV2Router), MAX);

        //exclude owner and this contract from fee
        _isExcludedFromFee[owner()] = true;
        _isExcludedFromFee[marketingAddress] = true;
        _isExcludedFromFee[developerAddress] = true;
        _isExcludedFromFee[charityAddress] = true;
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

    function minimumTokensBeforeSwapAmount() public view returns (uint256) {
        return minimumTokensBeforeSwap;
    }

    // Validation function to ensure the total fee is capped at 5%
    function _validateTotalFees() internal view {
        uint256 totalFees = 
            _burnFee + _reflectionFee + _liquidityPoolFee + _marketingFee + _developerFee + _charityFee;
        require(totalFees <= MAX_TOTAL_FEES, "Total fees exceed the 5% limit.");
    }

    function setBurnFee(uint256 burnFee_) external onlyOwner {
        require(burnFee_ <= MAX_BURN_FEE, "Burn fee exceeds the 1% limit.");
        _validateTotalFees();
        uint256 oldBurnFee = _burnFee;
        _burnFee = burnFee_;
        emit BurnFeeUpdated(oldBurnFee, burnFee_);
    }

    function setLiquidityPoolFee(uint256 liquidityPoolFee_) external onlyOwner {
        require(liquidityPoolFee_ <= MAX_FEE_INDIVIDUAL, "Liquidity pool fee exceeds the 2% limit.");
        _validateTotalFees();
        uint256 combinedLiquidityFee_ = liquidityPoolFee_ + _marketingFee + _developerFee + _charityFee;
        require(combinedLiquidityFee_ >= MIN_COMBINED_LIQUIDITY_FEE, "Combined liquidity fee cannot be zero.");
        uint256 oldLiquidityPoolFee = _liquidityPoolFee;
        _liquidityPoolFee = liquidityPoolFee_;
        _combinedLiquidityFee = combinedLiquidityFee_;
        emit LiquidityPoolFeeUpdated(oldLiquidityPoolFee, liquidityPoolFee_);
    }

    function setMarketingFee(uint256 marketingFee_) external onlyOwner {
        require(marketingFee_ <= MAX_FEE_INDIVIDUAL, "Marketing fee exceeds the 2% limit.");
        _validateTotalFees();
        uint256 combinedLiquidityFee_ = _liquidityPoolFee + marketingFee_ + _developerFee + _charityFee;
        require(combinedLiquidityFee_ >= MIN_COMBINED_LIQUIDITY_FEE, "Combined liquidity fee cannot be zero.");
        uint256 oldMarketingFee = _marketingFee;
        _marketingFee = marketingFee_;
        _combinedLiquidityFee = combinedLiquidityFee_;
        emit MarketingFeeUpdated(oldMarketingFee, marketingFee_);
    }

    function setDeveloperFee(uint256 developerFee_) external onlyOwner {
        require(developerFee_ <= MAX_FEE_INDIVIDUAL, "Dev fee exceeds the 2% limit.");
        _validateTotalFees();
        uint256 combinedLiquidityFee_ = _liquidityPoolFee + _marketingFee + developerFee_ + _charityFee;
        require(combinedLiquidityFee_ >= MIN_COMBINED_LIQUIDITY_FEE, "Combined liquidity fee cannot be zero.");
        uint256 oldDeveloperFee = _developerFee;
        _developerFee = developerFee_;
        _combinedLiquidityFee = combinedLiquidityFee_;
        emit DeveloperFeeUpdated(oldDeveloperFee, developerFee_);
    }

    function setCharityFee(uint256 charityFee_) external onlyOwner {
        require(charityFee_ <= MAX_FEE_INDIVIDUAL, "Charity fee exceeds the 2% limit.");
        _validateTotalFees();
        uint256 combinedLiquidityFee_ = _liquidityPoolFee + _marketingFee + _developerFee + charityFee_;
        require(combinedLiquidityFee_ >= MIN_COMBINED_LIQUIDITY_FEE, "Combined liquidity fee cannot be zero.");
        uint256 oldCharityFee = _charityFee;
        _charityFee = charityFee_;
        _combinedLiquidityFee = combinedLiquidityFee_;
        emit CharityFeeUpdated(oldCharityFee, charityFee_);
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

    function setCharityAddress(address _charityAddress) external onlyOwner {
        require(_charityAddress != address(0), "Charity address cannot be the zero address");
        address oldAddress = charityAddress;
        charityAddress = payable(_charityAddress);
        emit CharityAddressUpdated(oldAddress, _charityAddress);
    }

    function setSwapAndLiquifyEnabled(bool _enabled) public onlyOwner {
        swapAndLiquifyEnabled = _enabled;
        emit SwapAndLiquifyEnabledUpdated(_enabled);
    }

    function setMaxTxAmount(uint256 maxTxAmount) external onlyOwner {
        require(
            maxTxAmount >= (_tTotal * 1) / 1000,  // Ensure maxTxAmount is at least 0.1% of total supply
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

    function setReflectionFee(uint256 newReflectionFee) public onlyOwner {
        require(newReflectionFee <= MAX_FEE_INDIVIDUAL, "Reflection fee exceeds the 2% limit.");
        _validateTotalFees();
        uint256 oldReflectionFee = _reflectionFee;
        _reflectionFee = newReflectionFee;
        emit ReflectionFeeUpdated(oldReflectionFee, newReflectionFee);
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
        require(account != address(this), "Contract address cannot be excluded from reflection");
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
        if (_combinedLiquidityFee == 0) return; // Ensure _combinedLiquidityFee is non-zero

        uint256 initialBalance = address(this).balance;
        uint256 lpTokenBalance = (contractTokenBalance * _liquidityPoolFee) /
            _combinedLiquidityFee;

        uint256 liquidityHalf = lpTokenBalance / 2;
        uint256 otherLiquidityHalf = lpTokenBalance - liquidityHalf;
        
        swapTokensForEth(contractTokenBalance - otherLiquidityHalf);

        uint256 transferredBalance = address(this).balance - initialBalance;
        
        uint256 marketingShare = ((transferredBalance) * (_marketingFee * 10)) /
            (_combinedLiquidityFee * 10 - ((_liquidityPoolFee * 10) / 2));
        transferToAddressETH(marketingAddress, marketingShare);
        
        uint256 developerShare = ((transferredBalance) * (_developerFee * 10)) /
            (_combinedLiquidityFee * 10 - ((_liquidityPoolFee * 10) / 2));
        transferToAddressETH(developerAddress, developerShare);

        uint256 liquidityBalance = ((transferredBalance * _liquidityPoolFee * 10) / 2) /
            ((_combinedLiquidityFee * 10) - ((_liquidityPoolFee * 10) / 2));
        addLiquidity(otherLiquidityHalf, liquidityBalance);

        emit SwapAndLiquify(
            liquidityHalf,
            liquidityBalance,
            otherLiquidityHalf
        );

        uint256 charityShare = transferredBalance - marketingShare - developerShare - liquidityBalance;
        transferToAddressETH(charityAddress, charityShare);
    }

    function swapTokensForEth(uint256 tokenAmount) private {
        // generate the uniswap pair path of token -> weth
        address[] memory path = new address[](2);
        path[0] = address(this);
        path[1] = uniswapV2Router.WETH();

        // make the swap
        uniswapV2Router.swapExactTokensForETHSupportingFeeOnTransferTokens(
            tokenAmount,
            0, // accept any amount of ETH
            path,
            address(this), // The contract
            block.timestamp
        );

        emit SwapTokensForETH(tokenAmount, path);
    }

    function swapETHForTokens(uint256 amount) private {
        // generate the uniswap pair path of token -> weth
        address[] memory path = new address[](2);
        path[0] = uniswapV2Router.WETH();
        path[1] = address(this);

        // make the swap
        uniswapV2Router.swapExactETHForTokensSupportingFeeOnTransferTokens{
            value: amount
        }(
            0, // accept any amount of Tokens
            path,
            deadAddress, // Burn address
            block.timestamp + 300
        );

        emit SwapETHForTokens(amount, path);
    }

    function addLiquidity(uint256 tokenAmount, uint256 ethAmount) private {
        // add the liquidity
        uniswapV2Router.addLiquidityETH{value: ethAmount}(
            address(this),
            tokenAmount,
            0, // slippage is unavoidable
            0, // slippage is unavoidable
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
        _previousCharityFee = _charityFee;

        _combinedLiquidityFee = 0;
        _liquidityPoolFee = 0;
        _burnFee = 0;
        _reflectionFee = 0;
        _marketingFee = 0;
        _developerFee = 0;
        _charityFee = 0;
    }

    function restoreAllFee() private {
        _combinedLiquidityFee = _previousCombinedLiquidityFee;
        _liquidityPoolFee = _previousLiquidityPoolFee;
        _burnFee = _previousBurnFee;
        _reflectionFee = _previousReflectionFee;
        _marketingFee = _previousMarketingFee;
        _developerFee = _previousDeveloperFee;
        _charityFee = _previousCharityFee;
    }

    function presale(bool _presale) external onlyOwner {
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

    // Withdraw ETH that's potentially stuck in the Contract
    function recoverETHfromContract() external onlyOwner {
        uint ethBalance = address(this).balance;
        (bool succ, ) = payable(developerAddress).call{value: ethBalance}("");
        require(succ, "Transfer failed");
        emit AuditLog(
            "We have recovered the stock ETH from contract.",
            developerAddress
        );
    }

    // Withdraw ERC20 tokens that are potentially stuck in Contract
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
        emit Log("We have recovered tokens from contract:", _amount);
    }
}